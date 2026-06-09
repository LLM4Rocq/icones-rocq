# Goldens — Examples-shape chapter (Side/Headline/Status table)

## Beyond the paper — Phase 4 recursive examples (test fixture)

A miniature stand-in for the EXAMPLES.md "Phase 4" chapter.

### ex_geom (`ex_geom`, `ex_geom_denot_E`, `ex_geom_arr_mass_one`)

The fair-coin geometric distribution.

```coq
(* theories/programs/examples.v *)
Definition ex_geom : @named_expr R Ar R_obj nil tR' := ex_geom_body.
```

| Side | Headline | Status |
|---|---|---|
| CBV — total mass identity | `ex_geom_arr_mass_one` total mass = 1 | axiom-free |
| CBV — structural reduction | `ex_geom_denot_E` outer kcomp rewrite | axiom-free |
| CBN — total mass identity | `ex_geom_CBN_mass_one` total mass = 1 | axiom-free |

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
(* theories/programs/ppl_cbn_geom.v *)
Theorem ex_geom_CBN_mass_one :
  fmeas_mu ex_geom_CBN_fix [set: ar_carrier Ar R_obj] = 1%:E.
```

```coq
(* theories/programs/examples.v *)
Lemma ex_geom_denot_E :
  ex_geom_denot = kcomp (app_pair _) (em_pair ex_geom_body_denot (eD ne_tt)).
```
