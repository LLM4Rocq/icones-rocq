# EXAMPLES.md — surface programs and their CBV / CBN headlines

This document is the **Examples tab** of the auditor dashboard. Each entry
below documents one surface program from `theories/programs/examples.v`
(or `theories/programs/ex_even_odd.v`) together with the headline
mass / marginal / distribution theorems on both the CBV and CBN sides.

> **Note.** This file is a transitional placeholder. The full content —
> per-example surface syntax, intuition, and the verbatim headline
> theorem statements on both sides — is being written by a parallel
> agent and will land in a follow-up commit.

The PPL itself (the surface language, both interpretations, the
SCones↔tensor bridge, the value-fixpoint, the Bernoulli cascade
framework, the boolean cascade, mutual recursion) is on the
[PPL tab](../ppl/).

The paper-to-Rocq correspondence is on the [Paper tab](../paper/).

---

## Beyond the paper — Surface examples

The seven examples covered when this document is complete:

| Example | English | Rocq |
|---|---|---|
| `ex_random_constant` | A constant-output random function — distribution over `tfun tR' tR'`. | `examples.v::ex_random_constant`; CBV `ex_random_constant_mass`, `ex_random_constant_dist`; CBN `ex_random_constant_CBN_headline` |
| `ex_random_linear` | A linear random function `m·x + b` for `m, b ~ µ` — distribution over `tfun tR' tR'`. | `examples.v::ex_random_linear`; CBV `ex_random_linear_arith_marginal_at_CBV`; CBN `ex_random_linear_arith_marginal_at` |
| `ex_bayes_linear` | Bayesian posterior on a prior weighted by a score. | `examples.v::ex_bayes_linear`; CBV `ex_bayes_linear_is_weighted_headline`; CBN `ex_bayes_linear_CBN_headline` |
| `ex_loop` | Bare divergence. | `examples.v::ex_loop`; CBV `ex_loop_arr_mass_zero`; CBN `ex_loop_CBN_headline` |
| `ex_geom` | Geometric distribution with parameter 1/2. | `examples.v::ex_geom`; CBV `ex_geom_arr_mass_one` + `ex_geom_arr_is_geometric_distribution`; CBN `ex_geom_CBN_mass_one` + `ex_geom_CBN_PMF` |
| `ex_almost_loop_p` | Parameterised Bernoulli cascade; mass = 1 if `p > 0`, 0 otherwise. | `examples.v::ex_almost_loop`; CBV `ex_almost_loop_p_arr_mass_*`; CBN `ex_almost_loop_p_CBN_mass_*` and `_is_*` |
| `ex_even_odd_pair` | Mutually recursive even/odd at `tprod (tfun _ _) (tfun _ _)` via `ne_fix_mr`. | `ex_even_odd.v::ex_even_odd_pair`; CBV `ex_even_odd_pair_denot_E`; CBN `ex_even_odd_pair_denot_CBN_fix` |

Full per-example detail blocks with the surface-syntax code, the
intuition prose, and the verbatim theorem statements land in the
follow-up content commit.

---

## What is not formalised

No example-side gaps. The surface programs all have headline statements
on both CBV and CBN sides; the honest scope notes (`ex_random_linear`
CBV through `fmeas_lax_pre` rather than `kbind_ext_A`, `ex_bayes_linear`
CBN under option-γ, mutual-recursion CBV under the existing `Yfix_fun_T`
honest scope) are recorded on the PPL tab.

---

## How to verify

```sh
make -j
echo 'Print Assumptions Icones.programs.ppl_cbn_geom_dist.ex_geom_CBN_PMF.' \
  | rocq top -Q theories Icones
echo 'Print Assumptions Icones.programs.ppl_cbv_geom_dist.ex_geom_arr_is_geometric_distribution.' \
  | rocq top -Q theories Icones
```

Each command should report only the three `boolp` axioms inherited from
`mathcomp-analysis`.
