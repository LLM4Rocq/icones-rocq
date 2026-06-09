# EXAMPLES.md — End-to-end PPL example programs

Each surface program in `theories/programs/examples.v` and
`theories/programs/ex_even_odd.v` is reproduced here with its CBV and
CBN headline identities. The programs are written exclusively in the
direct-style `ppl_named` custom entry of `theories/programs/ppl.v`
(brackets `[ … ]` enter the entry; curly braces `{ x }` escape back
to plain Rocq). Every constructor of the language and every CBV /
CBN clause is exercised somewhere below.

The paper-side correspondence (§§ 2–9 ↔ Rocq) lives on the
[Paper tab](../paper/); the categorical-level PPL infrastructure
(the surface inductive, the two interpretations, the fixpoint
machinery) lives on the [PPL tab](../ppl/). This document covers the
**examples themselves**.

---

## QBS-style examples

The QBS-paper flagship programs. Three end-to-end probabilistic
programs that *do not* use recursion. Each one exercises a different
constructor of the language (`ne_let` + `ne_sample`, `ne_add` +
`ne_mul`, `ne_score`) and ships a structural reduction lemma on each
of the CBV and CBN sides.

| Paper-style label | English statement | Rocq |
|---|---|---|
| Constant random function | `let c := sample µ in λx. c` of type `tfun tR tR` denotes the QBS-flagship "distribution over a function space" (constant-output). | `ex_random_constant`, `ex_random_constant_denot_E` — `theories/programs/examples.v` |
| Random affine function | `let m := sample µ in let b := sample µ in λx. m·x + b` of type `tfun tR tR` denotes a random-coefficients linear regression model. | `ex_random_linear`, `ex_random_linear_denot_E` — same file |
| Unnormalised Bayesian posterior | `let m := sample µ in let _ := score f #"m" in #"m"` of type `tR` denotes the unnormalised posterior of total mass `∫ f(m) dµ(m)`. | `ex_bayes_linear`, `ex_bayes_linear_denot_E` — same file |

### ex_random_constant (`ex_random_constant`, `ex_random_constant_denot_E`, `ex_random_constant_mass`, `ex_random_constant_marginal_headline`, `ex_random_constant_dist`, `ex_random_constant_marginal_at`, `ex_random_constant_CBN_headline`, `ex_random_constant_CBN_marginal_mass`)

The QBS flagship constant-output random function. After sampling a
single random constant `c ~ µ`, the program returns the function
`λx. c` — every call to the function returns the same value, but the
function itself was sampled from `µ`. The headline correctness
statement is the *marginal at every `x`*: evaluating the function at
any test point recovers the prior `µ`.

```coq
(* theories/programs/examples.v *)
Definition ex_random_constant :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "c" := Sample (mu, Hmu) in \ "x" ::: tR' => # "c" ].
```

| Side | Headline | Status |
|---|---|---|
| CBV — structural reduction | `ex_random_constant_denot_E` (outer `kbind_ext`) | axiom-free |
| CBV — total-mass at every `x` | `ex_random_constant_mass`: `mass = µ(setT)` | axiom-free |
| CBV — marginal-at-`x` headline | `ex_random_constant_marginal_headline`: `= sample_kleisli µ Hµ` | axiom-free |
| CBV — distribution identity | `ex_random_constant_dist`: `= µ : FMeas R_obj` | axiom-free |
| CBV — pointwise marginal | `ex_random_constant_marginal_at U`: `= µ(U)` for every measurable `U` | axiom-free |
| CBN — structural reduction | `ex_random_constant_CBN_headline_struct` | axiom-free |
| CBN — marginal at every `x` | `ex_random_constant_CBN_headline`: `sh_fun (sc_fun ⟦…⟧ g) x = µ` | axiom-free |
| CBN — pointwise marginal mass | `ex_random_constant_CBN_marginal_mass`: `= µ(U)` | axiom-free |

```coq
(* theories/programs/examples.v *)
Lemma ex_random_constant_denot_E :
  ex_random_constant_denot =
  kbind_ext
    (eD ex_rc_lam)
    (sample_kleisli (ctxD (drop_names nil)) mu Hmu).
```

```coq
(* theories/programs/infra/ex_headlines.v *)
Theorem ex_random_constant_mass (x : R) :
  fmeas_mu
    (Lfun (der (FMeas R_obj))
          (Lfun (ch_mor
                   (kbind_ext (apply_at x) ex_random_constant_denot))
                (one1 : cone_one_car Ar)))
    [set: ar_carrier Ar R_obj]
  = fmeas_mu mu [set: ar_carrier Ar R_obj].
```

```coq
(* theories/programs/infra/ex_random_dist.v *)
Theorem ex_random_constant_dist (x : R) :
  Lfun (der (FMeas R_obj))
       (Lfun (ch_mor
                (kbind_ext (apply_at x) ex_random_constant_denot))
             (one1 : cone_one_car Ar))
  = mu :> FMeas R_obj.

Corollary ex_random_constant_marginal_at (x : R)
    (U : set (ar_carrier Ar R_obj)) :
  fmeas_mu (* … the marginal … *) U = fmeas_mu mu U.
```

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_random_constant_CBN_headline
    (g : ctxD_CBN (drop_names nil)) (Hg : (cone_norm g <= 1)%R)
    (x : FMeas R_obj) (Hx : (cone_norm x <= 1)%R) :
  sh_fun (sc_fun (eD_CBN_complete ex_random_constant) g) x = mu.
```

### ex_random_linear (`ex_random_linear`, `ex_random_linear_denot_E`, `ex_random_linear_mass`, `ex_random_linear_marginal_headline`, `ex_random_linear_arith_marginal_at_CBV`, `ex_random_linear_arith_marginal_at`)

A random-coefficients linear regression: sample slope `m` and
intercept `b` from `µ`, return the function `λx. m·x + b`. Exercises
`ne_add` and `ne_mul` via the FMeas lax-monoidal map of paper §5; on
Dirac inputs the lifts reduce to scalar arithmetic. The *killer
demo* — the headline marginal identity ties the surface program to
the joint pushforward of `µ ⊗ µ` along `(m, b) ↦ m·x + b`.

```coq
(* theories/programs/examples.v *)
Definition ex_random_linear :
    @named_expr R Ar R_obj nil (tfun tR' tR') :=
  [ let "m" := Sample (mu, Hmu) in
    let "b" := Sample (mu, Hmu) in
    \ "x" ::: tR' => # "m" * # "x" + # "b" ].
```

| Side | Headline | Status |
|---|---|---|
| CBV — structural reduction (nested `kbind_ext`) | `ex_random_linear_denot_E` | axiom-free |
| CBV — total mass at every `x` (= `µ(setT)²`) | `ex_random_linear_mass` | axiom-free |
| CBV — iterated-integral headline | `ex_random_linear_marginal_headline` (Shape A) | axiom-free |
| CBV — honest bilinear marginal | `ex_random_linear_arith_marginal_at_CBV` (NEW) | axiom-free |
| CBV — Dirac evaluation | `ex_random_linear_arith_dirac_E` | axiom-free |
| CBN — option-β marginal | `ex_random_linear_arith_marginal_at` (via the bridge) | axiom-free |
| CBN — option-γ degenerate marginal | `ex_random_linear_CBN_marginal_zero` (= `precone_zero`) | axiom-free |

```coq
(* theories/programs/examples.v *)
Lemma ex_random_linear_marginal_headline
    (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  fmeas_mu (fmeas_lax_pre mu mu) (arith_at_x_fun @^-1` U) =
    \int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
      \int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
        \d_(arith_at_x_fun (ar_prod_cast (m, b))) U.
```

```coq
(* theories/programs/infra/ex_random_dist.v *)
Theorem ex_random_linear_arith_marginal_at_CBV (x : R)
    (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  fmeas_mu (fmeas_lax_pre mu mu)
    ((arith_at_x_fun x) @^-1` U)
  = \int[fmeas_mu mu]_(m in [set: ar_carrier Ar R_obj])
       \int[fmeas_mu mu]_(b in [set: ar_carrier Ar R_obj])
         \d_(arith_at_x_fun x
              (ar_prod_cast (m, b))) U.
```

```coq
(* theories/programs/ppl_cbn_arith_eff.v *)
Theorem ex_random_linear_arith_marginal_at
    (arg : FMeas R_obj) (Harg : (cone_norm arg <= 1)%R) :
  sh_fun (sc_fun (eD_CBN_full_arith ex_random_linear) precone_zero) arg
  = add_FMeas (mul_FMeas mu arg) mu.
```

The CBN identity reads "the marginal at any unit-ball argument `arg`
is the honest bilinear lift `add_FMeas (mul_FMeas µ arg) µ`" —
recovering the QBS-paper-flagship "distribution over `λx. m·x + b`
for `m, b ∼ µ`" reading, instantiated at the option-β arithmetic.

### ex_bayes_linear (`ex_bayes_linear`, `ex_bayes_linear_denot_E`, `ex_bayes_linear_is_weighted`, `ex_bayes_linear_is_weighted_headline`, `ex_bayes_linear_CBN_headline`)

The textbook prior / score / observe shape of Bayesian inference:
sample a parameter `m` from the prior `µ`, score by a measurable
density `f(m) ∈ [0, 1]`, return `m`. Exercises `ne_score` and
delivers the unnormalised posterior of total mass `∫ f(m) dµ(m)`.

```coq
(* theories/programs/examples.v *)
Definition ex_bayes_linear :
    @named_expr R Ar R_obj nil tR' :=
  [ let "m" := Sample (mu, Hmu) in
    let "_" := Score { f, Hf_meas, Hf_ge0, Hf_le1 } # "m" in
    # "m" ].
```

| Side | Headline | Status |
|---|---|---|
| CBV — structural reduction (outer `kbind_ext`) | `ex_bayes_linear_denot_E` | axiom-free |
| CBV — Law-3 reduced shape | `ex_bayes_linear_is_weighted` (= `kcomp K (sample_kleisli µ Hµ)`) | axiom-free |
| CBV — measure-level posterior (Gap D) | `ex_bayes_linear_is_weighted_headline`: `=  ∫_(m∼µ) f(cR m) · δ_m U` | axiom-free |
| CBN — marginal identity | `ex_bayes_linear_CBN_headline`: `= µ` (under option-γ; score lands in terminal) | axiom-free |
| CBN — mass corollary | `ex_bayes_linear_CBN_mass`: `= µ(U)` | axiom-free |

```coq
(* theories/programs/examples.v *)
Lemma ex_bayes_linear_is_weighted :
  ex_bayes_linear_denot =
  kcomp (coalg_comp (eD ex_bl_cont)
                    (em_pair (em_term_mor _) (coalg_id _)))
        (sample_kleisli (ctxD (drop_names nil)) mu Hmu).

Lemma ex_bayes_linear_is_weighted_headline
    (U : set (ar_carrier Ar R_obj)) :
  measurable U ->
  fmeas_mu
    (Lfun (icones_comp (der (FMeas R_obj)) (ch_mor K_score)) mu) U
  = \int[fmeas_mu mu]_(m in @setT (ar_carrier Ar R_obj))
      ((f (cR m))%:E * \d_(m) U).
```

The CBV "Gap D" measure-level Bayes headline. The `der ∘ K_score`
action on `µ` reads as the weighted Dirac integral
`∫ f(cR m) · δ_m dµ(m)` — exactly the unnormalised posterior.

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_bayes_linear_CBN_headline
    (g : ctxD_CBN (drop_names nil))
    (Hg : (cone_norm g <= 1)%R) :
  sc_fun (eD_CBN_complete ex_bayes_linear) g = mu.
```

The CBN side under option-γ: since `tyD_CBN tunit = Stop` is the
terminal, `score` collapses to the terminal map and the program's
denotation reduces to the prior `µ` itself. This is the honest
statement at the option-γ baseline; the option-β refinement would
expose the genuine weighted posterior at the SCones level (still
pending — see *What is not formalised* below).

---

## Phase 4 — Recursive examples (productive partial termination)

Recursive probabilistic programs combining `ne_fix` (the CBV
value-fixpoint of `theories/programs/infra/em_fix.v`) with the
`ne_if` / `ne_bernoulli` boolean cascade to exhibit *productive
partial termination*. Each program ships with a structural CBV
reduction lemma exposing the outer `Yfix_fun_T` shape, plus the
honest mass identity on both interpretations.

| Paper-style label | English statement | Rocq |
|---|---|---|
| Bare divergence | `(let rec l = λ_. l ()) ()` of type `tunit`, total mass `0`. | `ex_loop`, `ex_loop_denot`, `ex_loop_arr_mass_zero`, `ex_loop_CBN_headline` — `theories/programs/examples.v` + `theories/programs/infra/ex_loop_arr.v` + `theories/programs/ppl_cbn_headlines.v` |
| Geometric distribution (THE PRIZE) | `(let rec g = λ_. if Bernoulli(½) then 0 else 1 + g ()) ()` of type `tR'`, geometric distribution with parameter `½`. | `ex_geom`, `ex_geom_denot_E`, `ex_geom_arr_mass_one`, `ex_geom_arr_is_geometric_distribution`, `ex_geom_CBN_mass_one`, `ex_geom_CBN_PMF` — `examples.v` + `em_fix_arr.v` + `ppl_cbv_geom_dist.v` + `ppl_cbn_geom.v` + `ppl_cbn_geom_dist.v` |
| Parameterised partial termination | `(let rec l = λ_. if Bernoulli(p) then () else l ()) ()` of type `tunit`. | `ex_almost_loop`, `ex_almost_loop_denot_E`, `ex_almost_loop_p_arr_mass_one_if_pos`, `ex_almost_loop_p_arr_mass_zero_if_zero`, `ex_almost_loop_p_CBN_mass_one_if_pos`, `ex_almost_loop_p_CBN_mass_zero_if_zero`, `ex_almost_loop_p_CBN_is_dirac_zero`, `ex_almost_loop_p_CBN_is_zero_if_zero` — `examples.v` + `ex_almost_loop_step.v` + `ppl_cbn_almost_loop.v` + `ppl_cbn_almost_loop_dist.v` |

### ex_loop (`ex_loop`, `ex_loop_denot`, `ex_loop_arr_mass_zero`, `ex_loop_CBN_headline`)

Bare divergence: `let rec l = λ_. l () in l ()`. No effect, no
sampling, no scoring — just an infinite chain of unit-typed
recursive calls. The CBV side has total mass `0` (the recursion
never terminates); the CBN side trivially equals the terminal map
(`tunit`'s denotation is `Stop`, a singleton).

```coq
(* theories/programs/examples.v *)
Definition ex_loop :
    @named_expr R Ar R_obj nil tunit :=
  [ (fix "l" ::: tfun tunit tunit in \ "_" ::: tunit => # "l" @ ()) @ () ].
```

| Side | Headline | Status |
|---|---|---|
| CBV — bare divergence (mass zero) | `ex_loop_arr_mass_zero`: `(c1_val (F_arr_loop n))%:num = 0` | axiom-free |
| CBN — terminal-uniqueness | `ex_loop_CBN_headline`: `= ders (Stop_mor _)` | axiom-free |

```coq
(* theories/programs/infra/ex_loop_arr.v *)
Theorem ex_loop_arr_mass_zero (n : nat) :
  (c1_val (F_arr_loop n))%:num = 0%R.
```

The Bang-level Kleene cascade `F_arr_loop n` has scalar value `0` at
every finite iterate `n` (the bare recursion never halts), and so
does its supremum by continuity.

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_loop_CBN_headline :
  eD_CBN_complete ex_loop =
  ders (Stop_mor (ctxD_CBN (drop_names nil))).
```

CBN-side trivial: codomain is `Stop Ar`, a singleton, so any two
arrows into it are equal by terminality.

### ex_geom (`ex_geom`, `ex_geom_denot_E`, `ex_geom_arr_mass_one`, `ex_geom_arr_is_geometric_distribution`, `ex_geom_CBN_mass_one`, `ex_geom_CBN_PMF`)

**The Prize.** A geometric counter built via a fair-coin Bernoulli
recursion: each call halts with probability `½` (returning `0`) and
otherwise recurses, adding `1` to the returned real. The program
denotes the genuine geometric distribution with parameter `½` —
total mass `1` and PMF `(1/2)^{k+1}` at every `k`. To our
knowledge, the first mass identity *and* the first PMF identity for
a recursive PPL example formalised in the integrable-cones model.

```coq
(* theories/programs/examples.v *)
Definition ex_geom : @named_expr R Ar R_obj nil tR' :=
  [ (fix "g" ::: tfun tunit tR' in
       \ "_" ::: tunit =>
         (if Bernoulli { (1 / 2 : R), phase4_half_ge0, phase4_half_le1 }
          then [| 0%R |]
          else [| 1%R |] + # "g" @ ())) @ () ].
```

| Side | Headline | Status |
|---|---|---|
| CBV — structural reduction | `ex_geom_denot_E`: outer `kcomp (app_pair _) (em_pair (Yfix_fun_T body) (eD ne_tt))` | axiom-free |
| CBV — total mass identity | `ex_geom_arr_mass_one`: `mass = 1` | axiom-free |
| CBV — geometric PMF | `ex_geom_arr_is_geometric_distribution`: `mass({k}) = (1/2)^{k+1}` | axiom-free |
| CBN — total mass identity | `ex_geom_CBN_mass_one`: `mass = 1` | axiom-free |
| CBN — geometric PMF | `ex_geom_CBN_PMF`: `mass({k}) = (1/2)^{k+1}` | axiom-free |
| CBN — structural reduction | `ex_geom_CBN_headline`: outer `Ev ∘ spair (Yfix ∘ curry body) (ders Stop_mor)` | axiom-free |

**Theorem (geometric distribution headline, CBV and CBN).** *Both
the CBV and the CBN denotation of `ex_geom` match the geometric
distribution with parameter `½` at every `k ∈ ℕ`: the mass at the
singleton `{k}` is `(1/2)^{k+1}`. In particular the total mass is
`1`.*

```coq
(* theories/programs/infra/em_fix_arr.v *)
Theorem ex_geom_arr_mass_one :
  fmeas_mu (Lfun (der (FMeas R_obj))
                 (linhom_fun (Lfun (der L_geom) Yfix_arr')
                             (one1 : cone_one_car Ar)))
           [set: ar_carrier Ar R_obj]
  = 1%:E.

(* theories/programs/ppl_cbv_geom_dist.v *)
Theorem ex_geom_arr_is_geometric_distribution (k : nat) :
  fmeas_mu
    (Lfun (der (FMeas R_obj))
          (linhom_fun (Lfun (der L_geom) Yfix_arr')
                      (one1 : cone_one_car Ar)))
    [set R_to_carrier R_carrier_eq k%:R]
  = ((1 / 2)%R ^+ k.+1)%R%:E.
```

The Bang-level Kleene cascade `F_arr n` of `em_fix_arr.v` has the
closed form
`mass(F_arr n) = 1 − (1/2)^n` (geometric series) and at the singleton
`{k}` it is eventually equal to `(1/2)^{k+1}`. Both identities pass
to the limit via `cone_sup_ball` monotone convergence.

```coq
(* theories/programs/ppl_cbn_geom.v *)
Theorem ex_geom_CBN_mass_one :
  fmeas_mu ex_geom_CBN_fix [set: ar_carrier Ar R_obj] = 1%:E.

(* theories/programs/ppl_cbn_geom_dist.v *)
Theorem ex_geom_CBN_PMF (k : nat) :
  fmeas_mu (ex_geom_CBN_fix R_carrier_eq R_carrier_meas R_to_carrier_meas)
           [set R_to_carrier R_carrier_eq k%:R]
  = ((1 / 2)%R ^+ k.+1)%R%:E.
```

The CBN side uses the same Kleene cascade `1 − (1/2)^n`, replayed at
the SCones level via the `phi_bcascade` framework of *The
Bernoulli-cascade framework* on the PPL tab. Both interpretations
agree pointwise.

```coq
(* theories/programs/ppl_cbn_headlines.v *)
Lemma ex_geom_CBN_headline :
  eD_CBN_complete ex_geom =
  scones_comp (Ev (Stop Ar) (FMeas R_obj))
    (spair (scones_comp (Yfix (stablehom (Stop Ar) (FMeas R_obj)))
                        (curry (eD_CBN_complete ex_geom_body)))
           (ders (Stop_mor (Stop Ar)))).
```

### ex_almost_loop_p (`ex_almost_loop`, `ex_almost_loop_denot_E`, `ex_almost_loop_p_arr_mass_one_if_pos`, `ex_almost_loop_p_arr_mass_zero_if_zero`, `ex_almost_loop_p_CBN_mass_one_if_pos`, `ex_almost_loop_p_CBN_mass_zero_if_zero`, `ex_almost_loop_p_CBN_is_dirac_zero`, `ex_almost_loop_p_CBN_is_zero_if_zero`)

A parameterised Bernoulli cascade: with probability `p` the
recursion halts (returning `()`) and with probability `1 − p` it
recurses. When `p > 0` the function terminates almost surely (total
mass `1`); when `p = 0` it diverges (total mass `0`). The dichotomy
is encoded in two pairs of headline theorems on each side.

```coq
(* theories/programs/examples.v *)
Definition ex_almost_loop (p : R)
    (Hp_ge0 : (0 <= p)%R) (Hp_le1 : (p <= 1)%R) :
    @named_expr R Ar R_obj nil tunit :=
  [ (fix "l" ::: tfun tunit tunit in
       \ "_" ::: tunit =>
         (if Bernoulli { p, Hp_ge0, Hp_le1 }
          then ()
          else # "l" @ ())) @ () ].
```

| Side | Headline | Status |
|---|---|---|
| CBV — structural reduction | `ex_almost_loop_denot_E` | axiom-free |
| CBV — mass = 1 if `p > 0` | `ex_almost_loop_p_arr_mass_one_if_pos` | axiom-free |
| CBV — mass = 0 if `p = 0` | `ex_almost_loop_p_arr_mass_zero_if_zero` | axiom-free |
| CBN — mass = 1 if `p > 0` | `ex_almost_loop_p_CBN_mass_one_if_pos` | axiom-free |
| CBN — mass = 0 if `p = 0` | `ex_almost_loop_p_CBN_mass_zero_if_zero` | axiom-free |
| CBN — fixpoint is Dirac at 0 (`p > 0`) | `ex_almost_loop_p_CBN_is_dirac_zero` | axiom-free |
| CBN — fixpoint is zero (`p = 0`) | `ex_almost_loop_p_CBN_is_zero_if_zero` | axiom-free |
| CBN — terminal-uniqueness wrapper | `ex_almost_loop_CBN_headline`: `= ders (Stop_mor _)` | axiom-free |

```coq
(* theories/programs/infra/ex_almost_loop_step.v *)
Theorem ex_almost_loop_p_arr_mass_one_if_pos :
  (0 < p)%R ->
  (c1_val F_arr_loop_p_sup)%:num = 1%R.

Theorem ex_almost_loop_p_arr_mass_zero_if_zero :
  p = 0%R ->
  (c1_val F_arr_loop_p_sup)%:num = 0%R.
```

The CBV side runs at the `Bang` level: the Kleene cascade
`F_arr_loop_p n` has closed form `c1_val = 1 − (1−p)^n` (geometric
series in `1 − p`); for `p > 0` it converges to `1`, for `p = 0` it
is identically `0`.

```coq
(* theories/programs/ppl_cbn_almost_loop.v *)
Theorem ex_almost_loop_p_CBN_mass_one_if_pos :
  (0 < p)%R ->
  fmeas_mu ex_almost_loop_p_CBN_fix [set: ar_carrier Ar R_obj] = 1%:E.

Theorem ex_almost_loop_p_CBN_mass_zero_if_zero :
  p = 0%R ->
  fmeas_mu ex_almost_loop_p_CBN_fix [set: ar_carrier Ar R_obj] = 0%E.
```

The CBN side recovers the same closed form via the `phi_bcascade`
framework instantiated at `halt := δ_0`, `cont_op := scones_id`.

```coq
(* theories/programs/ppl_cbn_almost_loop_dist.v *)
Theorem ex_almost_loop_p_CBN_is_dirac_zero :
  (0 < p)%R ->
  ex_almost_loop_p_CBN_fix R_carrier_eq p Hp_ge0 Hp_le1 = halt_alp_.

Theorem ex_almost_loop_p_CBN_is_zero_if_zero :
  p = 0%R ->
  ex_almost_loop_p_CBN_fix R_carrier_eq p Hp_ge0 Hp_le1 =
  (precone_zero : FMeas R_obj).
```

The "is" statements are stronger than the mass identities: the
fixpoint *is* the Dirac at `0` (resp. `precone_zero`) — not just an
arbitrary measure with the right mass. Proved by extensional
measure equality via the kleene-cascade convergence at every
measurable set.

---

## Mutual recursion — Beyond ne_fix at function types

The mutual-recursion shape `tprod (tfun A1 B1) (tfun A2 B2)` (paper
*not covered*; introduced as `ne_fix_mr` in `ppl.v` together with
`is_free_coalg_type`). The expert's note (per project memory)
reads: *"ça marche sur les types dont l'interprétation est une
coalgèbre libre, ce qui inclut aussi les produits de types fonction
et permet de définir des fonctions mutuellement récursives."*
Translation: CBV value-fixpoints at function types extend to body
types whose interpretation is a *free* `!`-coalgebra; this class
includes products of function types, which is exactly what enables
mutual recursion.

| Paper-style label | English statement | Rocq |
|---|---|---|
| Mutually recursive function pair | `fix_mr "p" as tprod (tfun tR tR) (tfun tR tR) by erefl in (λn. snd #"p" @ #"n", λn. fst #"p" @ #"n")` of type `tprod (tfun tR tR) (tfun tR tR)`. | `ex_even_odd_pair`, `ex_even`, `ex_odd` — `theories/programs/ex_even_odd.v` |

### ex_even_odd_pair (`ex_even_odd_pair`, `ex_even_odd_lam_a`, `ex_even_odd_lam_b`, `ex_even`, `ex_odd`, `ex_even_odd_pair_denot_E`, `ex_even_odd_pair_denot_CBN_E`, `ex_even_odd_pair_denot_CBN_fix`)

A mutually-recursive pair of functions on `tR`: bound under a
single recursive name `p` of type `tprod (tfun tR tR) (tfun tR tR)`
(a free-coalgebra type, witnessed by `erefl : is_free_coalg_type _
= true`), the two components delegate to each other via the `fst`
/ `snd` projections. Operationally this diverges everywhere (each
component immediately calls the other); the headline of this
example is *typing* + *CBN soundness*, not termination.

```coq
(* theories/programs/ex_even_odd.v *)
Definition ex_even_odd_lam_a :
    @named_expr R Ar R_obj (("p"%string, pair_ty) :: nil)
                            (tfun tR' tR') :=
  [ \ "n" ::: tR' => snd # "p" @ # "n" ].

Definition ex_even_odd_lam_b :
    @named_expr R Ar R_obj (("p"%string, pair_ty) :: nil)
                            (tfun tR' tR') :=
  [ \ "n" ::: tR' => fst # "p" @ # "n" ].

Definition ex_even_odd_pair :
    @named_expr R Ar R_obj nil pair_ty :=
  [ fix_mr "p" as pair_ty by erefl
       in ({ex_even_odd_lam_a}, {ex_even_odd_lam_b}) ].

Definition ex_even :
    @named_expr R Ar R_obj nil (tfun tR' tR') := [ fst {ex_even_odd_pair} ].
Definition ex_odd  :
    @named_expr R Ar R_obj nil (tfun tR' tR') := [ snd {ex_even_odd_pair} ].
```

The two pre-named lambdas are pulled out of the surface pair
because the `ppl_named` pair notation `(M, N)` requires each
component at custom level 60, and the lambda notation
`\ x ::: A => …` sits at level 70 > 60; splicing the lambdas back
through the `{ … }`-escape is the surface-syntax workaround.

| Side | Headline | Status |
|---|---|---|
| CBV — structural reduction (honest-scope at `tprod`) | `ex_even_odd_pair_denot_E`: `= const_kleisli precone_zero` | axiom-free |
| CBN — structural reduction (Yfix at `tprod`) | `ex_even_odd_pair_denot_CBN_E`: `= scones_comp (Yfix _) (curry body)` | axiom-free |
| CBN — Yfix soundness for `ne_fix_mr` | `ex_even_odd_pair_denot_CBN_fix`: pointwise fixpoint equation on the unit ball | axiom-free |

```coq
(* theories/programs/ex_even_odd.v *)
Lemma ex_even_odd_pair_denot_E :
  ex_even_odd_pair_denot =
  @const_kleisli R Ar (ctxD (drop_names nil))
    (coalg_obj (EM_prod (tyD (tfun tR' tR')) (tyD (tfun tR' tR'))))
    precone_zero (precone_zero_norm_le1 _).
Proof. by []. Qed.
```

CBV — *honest scope at product types.* `Yfix_mr_pack` at `tprod` is
the documented constant-zero placeholder of `ppl.v` (see *Dispatcher
for `ne_fix_mr`* on the PPL tab). The lemma is delivered as a
single-line `by [].`: the structural reduction exposes precisely
this placeholder, so the user can read off that the CBV side is
honest-scope deferred.

```coq
(* theories/programs/ex_even_odd.v *)
Lemma ex_even_odd_pair_denot_CBN_E :
  ex_even_odd_pair_denot_CBN =
  scones_comp (Yfix (tyD_CBN pair_ty))
              (curry (eD_CBN' ex_even_odd_body)).
Proof. by []. Qed.

Lemma ex_even_odd_pair_denot_CBN_fix
    (g : ctxD_CBN (drop_names nil)) (Hg : (cone_norm g <= 1)%R) :
  sh_fun (sc_fun (curry (eD_CBN' ex_even_odd_body)) g)
         (sc_fun ex_even_odd_pair_denot_CBN g) =
  sc_fun ex_even_odd_pair_denot_CBN g.
```

CBN — *fully sound mutual recursion.* The `Yfix`-soundness identity
transports unchanged from `eD_CBN_fix_mr_E`: at any `g` in the unit
ball, applying the body's curry at `g` to the
`ex_even_odd_pair_denot_CBN` at `g` returns the
`ex_even_odd_pair_denot_CBN` at `g` itself. This is *genuine*
mutual recursion — the body's curry has both projection slots
`fst #"p"` / `snd #"p"` simultaneously available through the
rec-bound name `p`, and the `Yfix`-fixpoint of paper §9.2 works
unconditionally at any `ICone.type Ar`, including the product cone
`stablehom (tyD_CBN tR) (tyD_CBN tR) × stablehom (tyD_CBN tR)
(tyD_CBN tR)`.

---

## What is **not** formalised

| Item | What it is | Why not yet |
|---|---|---|
| CBV `ex_random_linear` marginal at the `kbind_ext_A` bridge level | The QBS-paper-flagship marginal identity for `ex_random_linear` at the *inner* `kbind_ext` level (joining the two prior bindings into a single FMeas-lax pushforward). | Requires Law 2 (`kbind_ext_A`) + cartesian uniqueness in `EM(!)` exposed at the `icones_hom` level; closed at the *measure level* via `ex_random_linear_arith_marginal_at_CBV` (which sidesteps the inner `kbind_ext` by working with `fmeas_lax_pre` directly). |
| Option-α unit-type refinement | Replace `tyD_CBN tunit := Stop` by `Bang(FMeas *)` so `ne_score` does not collapse to a constant under CBN. | Needs a parallel `eD_CBN_full_alpha` interpretation and clauses; the option-β refinement of arithmetic (already shipped) is independent and orthogonal. |
| CBV mutual recursion at product types | `Yfix_mr_pack` at `tprod` is currently a constant-zero placeholder. | Requires a `Bang`-level Kleene cascade at `tprod` (the natural product of two `Yfix_fun_T`s plus a Seely-2-iso untangling). CBN side already fully sound via `Yfix` at the product cone. |

These choices are deliberate; each requires substantial
infrastructure outside the current scope and does not block any
*existing* headline result.

---

## How to verify

```sh
make -j

# QBS-style examples
echo "Print Assumptions ex_random_constant_denot_E."    | \
  rocq top -Q theories Icones -l theories/programs/examples.v
echo "Print Assumptions ex_random_constant_dist."       | \
  rocq top -Q theories Icones -l theories/programs/infra/ex_random_dist.v
echo "Print Assumptions ex_random_linear_arith_marginal_at_CBV." | \
  rocq top -Q theories Icones -l theories/programs/infra/ex_random_dist.v
echo "Print Assumptions ex_random_linear_arith_marginal_at."     | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_arith_eff.v
echo "Print Assumptions ex_bayes_linear_is_weighted_headline." | \
  rocq top -Q theories Icones -l theories/programs/examples.v
echo "Print Assumptions ex_bayes_linear_CBN_headline." | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_headlines.v

# Phase 4 recursive examples
echo "Print Assumptions ex_loop_arr_mass_zero."         | \
  rocq top -Q theories Icones -l theories/programs/infra/ex_loop_arr.v
echo "Print Assumptions ex_loop_CBN_headline."          | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_headlines.v
echo "Print Assumptions ex_geom_arr_mass_one."          | \
  rocq top -Q theories Icones -l theories/programs/infra/em_fix_arr.v
echo "Print Assumptions ex_geom_arr_is_geometric_distribution." | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbv_geom_dist.v
echo "Print Assumptions ex_geom_CBN_mass_one."          | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_geom.v
echo "Print Assumptions ex_geom_CBN_PMF."               | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_geom_dist.v
echo "Print Assumptions ex_almost_loop_p_arr_mass_one_if_pos." | \
  rocq top -Q theories Icones -l theories/programs/infra/ex_almost_loop_step.v
echo "Print Assumptions ex_almost_loop_p_CBN_mass_one_if_pos." | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_almost_loop.v
echo "Print Assumptions ex_almost_loop_p_CBN_is_dirac_zero."   | \
  rocq top -Q theories Icones -l theories/programs/ppl_cbn_almost_loop_dist.v

# Mutual recursion
echo "Print Assumptions ex_even_odd_pair_denot_E."      | \
  rocq top -Q theories Icones -l theories/programs/ex_even_odd.v
echo "Print Assumptions ex_even_odd_pair_denot_CBN_E."  | \
  rocq top -Q theories Icones -l theories/programs/ex_even_odd.v
echo "Print Assumptions ex_even_odd_pair_denot_CBN_fix." | \
  rocq top -Q theories Icones -l theories/programs/ex_even_odd.v
```

Each command reports only `propositional_extensionality`,
`functional_extensionality_dep` and
`constructive_indefinite_description` (the classical-logic axioms of
`mathcomp-analysis`). Per-entry pages embed the precise identifier
name, file, and a GitHub link to the Rocq source.

For the underlying surface inductive and the two interpretations,
see the [PPL tab](../ppl/) — `docs/PPL.md`. For the paper-side
correspondence (§§ 2–9 ↔ Rocq), see the [Paper tab](../paper/) —
`docs/PAPER.md`.
