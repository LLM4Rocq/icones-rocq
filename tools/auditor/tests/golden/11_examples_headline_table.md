# Goldens — Examples-shape chapter (Paper-style overview table)

## Recursive examples (test fixture)

A miniature stand-in for an EXAMPLES.md chapter.

### ex_geom (`ex_geom`, `ex_geom_denot_E`, `ex_geom_arr_mass_one`)

The fair-coin geometric distribution.

```coq
(* theories/programs/examples.v *)
Definition ex_geom : @named_expr R Ar R_obj nil tR' := ex_geom_body.
```

| Result | Statement | Rocq |
|---|---|---|
| Def (`ex_geom`) | The fair-coin geometric counter. | `ex_geom` — `theories/programs/examples.v` |
| Thm (`ex_geom_arr_mass_one`) | The denotation has total mass one. | `ex_geom_arr_mass_one` — `theories/programs/infra/em_fix_arr.v` |
| Lem (`ex_geom_denot_E`) | The outer application reduces structurally. | `ex_geom_denot_E` — `theories/programs/examples.v` |

```coq
(* theories/programs/infra/em_fix_arr.v *)
Theorem ex_geom_arr_mass_one :
  fmeas_mu (Lfun (der (FMeas R_obj))
                 (linhom_fun (Lfun (der L_geom) Yfix_arr')
                             (one1 : cone_one_car Ar)))
           [set: ar_carrier Ar R_obj]
  = 1%:E.
```

```coq
(* theories/programs/examples.v *)
Lemma ex_geom_denot_E :
  ex_geom_denot = kcomp (app_pair _) (em_pair ex_geom_body_denot (eD ne_tt)).
```
