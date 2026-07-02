# Paper-to-Rocq correspondence

This tab is for a **paper reviewer / mathematician** auditing the Icones
formalisation of Ehrhard–Geoffroy *"Integration in Cones"*. It maps each
definition / lemma / theorem of the paper to its Rocq counterpart, so you can
verify *what is formalised* without having to read the proof scripts
themselves.

Two companion tabs cover the **probabilistic programming language**
developed on top of the paper's categorical model: the [PPL tab](../ppl/)
gives the top-down narrative (the CBV interpretation via EM(!), the
fixpoint machinery, the semantic laws), and the
[Examples tab](../examples/) collects the worked surface programs and
their CBV headline lemmas. This document covers
the **paper** itself, plus the paper-cited meta-theorems we had to mechanize
to remove their black-box status (SAFT, EM(!) Cor 20, LNL adjunction).

The paper is:

> **Thomas Ehrhard and Guillaume Geoffroy**, *Integration in Cones*, LMCS **21**(1:1), 2025 —
> [DOI 10.46298/LMCS-21(1:1)2025](https://doi.org/10.46298/LMCS-21(1:1)2025) /
> [arXiv 2212.02371](https://arxiv.org/abs/2212.02371).

---

## How to read the Rocq references

Each Rocq name is given as `Module.path.name` plus the source file. To inspect
any of them in your local checkout:

```sh
# Type and definition
echo 'Print Icones.homs.seely.ICones_Seely.' | rocq top -Q theories Icones

# Axiom dependencies
echo 'Print Assumptions Icones.homs.seely.ICones_Seely.' \
  | rocq top -Q theories Icones
```

The whole formalisation depends only on the **three classical-logic axioms**
inherited from `mathcomp-analysis`: `propositional_extensionality`,
`functional_extensionality_dep`, `constructive_indefinite_description`.
There are **no project-specific axioms**, no `Admitted` proofs, no
`Parameter` interfaces anywhere in `theories/`. The script
[`./verify.sh`](./verify.sh) runs `Print Assumptions` on the
regression-anchor lemma `Skern_to_ICones_fully_faithful` (paper Theorem 6.5)
and a small set of downstream headline results.

---

## Paper § 2 — Cones

The paper introduces *positive cones* (an additive monoid with a non-negative
scalar action and a complete norm in the Selinger style). The formalisation
follows the same definitional path, packaged as a Hierarchy Builder tower.

| Paper | English statement | Rocq |
|---|---|---|
| Def 2.1 | A *precone* is an $\mathbb{R}_{\geq 0}$-semimodule with cancellative, positive addition; the *cone order* $x_1 \leq x_2$ holds iff $x_2 = x_1 + x$ for some $x$. | `precone`, `PreCone.type` — `theories/cones/precone.v` |
| Def 2.2 | A *cone* is a precone equipped with a norm $\lVert\cdot\rVert : P \to \mathbb{R}_{\geq 0}$ that is homogeneous, separating, sub-additive, order-monotone, and $\omega$-complete on norm-bounded increasing chains. | `Cone.type` — `theories/cones/cone.v` |
| Cat 2 | The category $\mathbf{Cones}$ has cones as objects and linear continuous maps $f$ with $\lVert f\rVert \leq 1$ as morphisms. | `cones_hom`, `cones_comp`, `Cones` (the category) — `theories/cones/cone_cat.v` |
| Lem 2.8 / 2.10 | $\omega$-continuity of the inverse of a bijective linear continuous map / of the difference $g - f$ of an increasing $f$ below an $\omega$-continuous $g$. | `invf_omega_continuous`, `diff_omega_continuous` — `theories/cones/basic_lemmas.v` |

Notable design choice: $\omega$-continuity comes in two flavours — `is_omega_continuous`
(input and output chains live in the unit ball; linear-tailored) and
`is_scott_continuous_unit` (input chain in the ball, output at any radius;
the *general* notion needed for non-linear stable maps in §7). Both are
proved equivalent for linear maps.

### Def 2.1 (`isPrecone` / `Precone`)

A *precone* is an $\mathbb{R}_{\geq 0}$-semimodule $P$ whose addition is cancellative and positive; these two conditions let one define the *cone order* $x_1 \leq x_2 \iff \exists x\, .\, x_2 = x_1 + x$, a partial order with a partial subtraction $x_2 - x_1$.

> **Paper — §2 "Basic definitions"** (arXiv 2212.02371, `content.tex:200`). A *precone* is an $\mathbb{R}_{\geq 0}$-semimodule $P$ which satisfies $$\forall x_1,x_2,x\in P\quad x_1+x=x_2+x\Rightarrow x_1=x_2$$ (cancellation) and $$\forall x_1,x_2\in P\quad x_1+x_2=0\Rightarrow x_1=0$$ (positivity). Given $x_1,x_2\in P$, one stipulates $x_1\leq x_2$ if $\exists x\in P\, .\, x_2=x_1+x$; this is a partial order, the *cone order* of $P$, and when $x_1\leq x_2$ there is exactly one $x$ with $x_2=x_1+x$, denoted $x_2-x_1$.

> **Difference.** The paper defines a precone as an $\mathbb{R}_{\geq 0}$-semimodule (the semimodule laws are left implicit); the formalization spells the semimodule structure out as explicit mixin fields (associativity, commutativity, unit, the two distributivities, scalar associativity, and the $0$/$1$ scalar laws) alongside the two paper axioms (cancellation) and (positivity). The cone order and subtraction are derived, not primitive.

```coq
(* theories/cones/precone.v *)
HB.mixin Record isPrecone (R : realType) (P : Type) := {
  precone_zero  : P;
  precone_add   : P -> P -> P;
  precone_scale : {nonneg R} -> P -> P;
  precone_addA : associative precone_add;
  precone_addC : commutative precone_add;
  precone_add0 : left_id precone_zero precone_add;
  precone_scale_DAr :
    forall r x y, precone_scale r (precone_add x y) =
                  precone_add (precone_scale r x) (precone_scale r y);
  precone_scale_DAl :
    forall (r s : {nonneg R}) x,
      precone_scale (r%:num + s%:num)%:nng x =
      precone_add (precone_scale r x) (precone_scale s x);
  precone_scale_A :
    forall (r s : {nonneg R}) x,
      precone_scale (r%:num * s%:num)%:nng x =
      precone_scale r (precone_scale s x);
  precone_scale_1  : forall x, precone_scale 1%:nng x = x;
  precone_scale_0r : forall r, precone_scale r precone_zero = precone_zero;
  precone_scale_0l : forall x, precone_scale 0%:nng x = precone_zero;
  precone_cancel :
    forall x y z, precone_add x y = precone_add x z -> y = z;
  precone_pos :
    forall x y, precone_add x y = precone_zero ->
                x = precone_zero /\ y = precone_zero;
}.

#[short(type="preconeType")]
HB.structure Definition Precone (R : realType) := { P of isPrecone R P }.
```

### Def 2.2 (`isCone` / `Cone`)

A *cone* is a precone $P$ equipped with a norm $\lVert\cdot\rVert : P \to \mathbb{R}_{\geq 0}$ subject to homogeneity (Normh), separation (Normz), sub-additivity (Normt), order-monotonicity (Normp), and $\omega$-completeness (Normc): every norm-bounded increasing $\omega$-chain has a least upper bound whose norm is again $\leq 1$.

> **Paper — §2 "Basic definitions"** (arXiv 2212.02371, `content.tex:221`). A *cone* is a precone $P$ equipped with a function $\lVert\cdot\rVert_P : P\to\mathbb{R}_{\geq 0}$, called the *norm of $P$*, satisfying: $$\text{(Normh)}\quad \forall \lambda\in\mathbb{R}_{\geq 0}\ \forall x\in P\quad \lVert\lambda x\rVert=\lambda\lVert x\rVert$$ $$\text{(Normz)}\quad \forall x\in P\quad \lVert x\rVert=0\Rightarrow x=0$$ $$\text{(Normt)}\quad \forall x_1,x_2\in P\quad \lVert x_1+x_2\rVert\leq\lVert x_1\rVert+\lVert x_2\rVert$$ $$\text{(Normp)}\quad \forall x_1,x_2\in P\quad \lVert x_1\rVert\leq\lVert x_1+x_2\rVert\quad(\text{equivalently } x_1\leq x_2\Rightarrow\lVert x_1\rVert\leq\lVert x_2\rVert)$$ $$\text{(Normc)}\quad \text{each increasing } (x_n)_{n\in\mathbb{N}} \text{ with } \forall n\ \lVert x_n\rVert\leq 1 \text{ has a lub } x=\sup_{n\in\mathbb{N}}x_n \text{ with } \lVert x\rVert\leq 1.$$

> **Difference.** The paper's completeness axiom (Normc) is a pure existence statement (the norm-bounded increasing chain *has* a lub of norm $\leq 1$). The formalization makes the least upper bound an explicit operator `cone_sup_ball` on the mixin, with its defining universal properties (`cone_sup_ball_ub` upper-bound, `cone_sup_ball_lub` least, `cone_sup_ball_norm` norm $\leq 1$) as separate fields — the constructive counterpart of "has a lub".

```coq
(* theories/cones/cone.v *)
HB.mixin Record isCone (R : realType) P of Precone R P := {
  cone_norm : P -> R;
  cone_normh : forall (r : {nonneg R}) (x : P),
    cone_norm (precone_scale r x) = r%:num * cone_norm x;
  cone_normz : forall x : P, cone_norm x = 0 -> x = precone_zero;
  cone_normt : forall x y : P,
    cone_norm (precone_add x y) <= cone_norm x + cone_norm y;
  cone_normp : forall x y : P,
    precone_le x y -> cone_norm x <= cone_norm y;
  cone_sup_ball :
    forall u : nat -> P,
      (forall n, precone_le (u n) (u n.+1)) ->
      (forall n, cone_norm (u n) <= 1) ->
      P;
  cone_sup_ball_ub :
    forall (u : nat -> P) (uch : _) (ub1 : _) n,
      precone_le (u n) (cone_sup_ball u uch ub1);
  cone_sup_ball_lub :
    forall (u : nat -> P) (uch : _) (ub1 : _) y,
      (forall n, precone_le (u n) y) ->
      precone_le (cone_sup_ball u uch ub1) y;
  cone_sup_ball_norm :
    forall (u : nat -> P) (uch : _) (ub1 : _),
      cone_norm (cone_sup_ball u uch ub1) <= 1;
}.

#[short(type="coneType")]
HB.structure Definition Cone (R : realType) :=
  { P of isCone R P & Precone R P }.
```

### Cat 2 (`cones_hom`, `cones_comp`, `Cones`)

The category $\mathbf{Cones}$ has cones as objects; a morphism $P \to Q$ is a linear, $\omega$-continuous map with operator norm $\leq 1$. The norm-nonexpansiveness is encoded pointwise as $\lVert f(x)\rVert \leq \lVert x\rVert$, which is equivalent to $\lVert f\rVert\leq 1$.

> **Paper — Definition 2.17** (arXiv 2212.02371). The category $\mathbf{Cones}$ has the cones as objects, and $\mathbf{Cones}(P,Q)$ is the set of all linear and continuous $f:P\to Q$ such that $\lVert f\rVert\leq 1$.

> **Difference.** The paper's morphism condition $\lVert f\rVert\leq 1$ is the operator norm $\sup_{x\in\mathbf{B}P}\lVert f(x)\rVert\leq 1$; the formalization records the pointwise inequality `cones_hom_norm_le1` : $\forall x\, .\, \lVert f(x)\rVert\leq\lVert x\rVert$, which is equivalent but avoids materialising the supremum.

```coq
(* theories/cones/cone_cat.v — Section ConesHom, Variables R Q P *)
Record cones_hom (P Q : coneType R) : Type := ConesHom {
  cones_hom_fun :> P -> Q;
  cones_hom_linear : is_linear cones_hom_fun;
  cones_hom_continuous : is_omega_continuous cones_hom_fun;
  cones_hom_norm_le1 :
    forall x : P, cone_norm (cones_hom_fun x) <= cone_norm x;
}.

Definition cones_comp (g : cones_hom Q S) (f : cones_hom P Q) :
  cones_hom P S.
Proof. (* refine (ConesHom (g \o f) ...) ; proof omitted *) Defined.
```

The category `Cones` is the locally-small category whose hom-type is
`cones_hom` and whose composition is `cones_comp`; it is not packaged as a
named record here (the project follows PLAN Strategy C: no abstract
`Category` typeclass).

### Lem 2.8 / 2.10 (`invf_omega_continuous`, `diff_omega_continuous`)

Two $\omega$-continuity lemmas: `invf_omega_continuous` shows the inverse of a bijective linear continuous map is $\omega$-continuous (paper Lemma 2.8), and `diff_omega_continuous` shows the difference $g - f$ of an increasing $f$ dominated by an $\omega$-continuous $g$, with $g - f$ increasing, is itself $\omega$-continuous (paper Lemma 2.10).

> **Paper — Lemma 2.8** (arXiv 2212.02371, `lemma:linear-inverse`). Let $P$ and $Q$ be cones and let $f:P\to Q$ be linear and continuous. If $f$ is bijective then $f^{-1}$ is linear and continuous.

> **Paper — Lemma 2.10** (arXiv 2212.02371, `lemma:fun-diff-Scott`). Let $P$ and $Q$ be cones, let $A\subseteq P$ be $\omega$-closed and let $f,g:A\to Q$ be functions such that $f$ is increasing, $g$ is $\omega$-continuous, $\forall x\in P\ f(x)\leq g(x)$ and the function $g-f=\boldsymbol\lambda x\in P\cdot (g(x)-f(x))$ is increasing. Then $g-f$ is $\omega$-continuous.

> **Difference.** The paper's Lemma 2.8 states that $f^{-1}$ is *linear and continuous*; the Rocq lemma `invf_omega_continuous` isolates the $\omega$-continuity component (linearity of the inverse is a separate result in the same section). Lemma 2.10 uses the general $\omega$-closed subdomain $A$; the formalization specialises the difference $g-f$ (there written `gmf`) to the ambient cone and expresses $\omega$-continuity via the explicit `cone_sup_ball` least-upper-bound operator, with the hypothesis $g = f + (g-f)$ recorded as `Hsplit`.

```coq
(* theories/cones/basic_lemmas.v *)
(* Section variables: R : realType, P Q : coneType R,
   f : P -> Q linear, omega-continuous, injective, surjective ;
   invf : Q -> P the section provided by surjectivity. *)
Lemma invf_omega_continuous : is_omega_continuous invf.

(* Section variables: R : realType, P Q : coneType R. *)
Lemma diff_omega_continuous
  (f g gmf : P -> Q)
  (Hf_incr   : is_increasing f)
  (Hg_cont   : is_omega_continuous g)
  (Hgmf_incr : is_increasing gmf)
  (Hsplit    : forall x, g x = precone_add (f x) (gmf x))
  (u : nat -> P) (uch : _) (ub1 : _)
  (gmfuch : _) (gmfub1 : _) (guch : _) (gub1 : _)
  (fxgmfuch : _) (fxgmfub1 : _) :
  gmf (cone_sup_ball u uch ub1) =
    cone_sup_ball (gmf \o u) gmfuch gmfub1.
```

---

## Paper § 3 — Measurable cones (MCones)

The paper bases measurability on a small full subcategory `ARCAT` of `MEAS`
(measurable spaces with measure-1 elements and finite products). The
formalisation packages `ARCAT` as a record so the entire §3+ tower is
*parametric in the chosen subcategory*.

| Paper | English statement | Rocq |
|---|---|---|
| `ARCAT` | A small full subcategory $\mathbf{Ar}$ of $\mathbf{Meas}$ closed under cartesian products and containing the one-point terminal object $0$, all of whose objects are non-empty. | `MeasSubcat`, `ar_obj`, `ar_carrier`, `ar_point`, `ar_zero`, `ar_prod` — `theories/mcones/ar.v` |
| Def 3.2 / 3.6 | A *measurable cone* is a cone $\underline{C}$ equipped with a *measurability structure* $\mathcal{M}=(\mathcal{M}_X)_{X\in\mathbf{Ar}}$ of test families satisfying (Msmeas), (Mscomp), (Mssep) and (Msnorm). | `MCone.type` (via `isMCone` mixin) — `theories/mcones/mcone.v` |
| Def 3.13 | An *mcones morphism* is a $\mathbf{Cones}$-morphism $f$ that sends measurable paths to measurable paths. | `mcones_hom`, `mcones_comp`, `MCones` — `theories/mcones/mcone_cat.v` |
| Prop 3.11 | Dual norm separation: $\lVert x\rVert = \sup_{x' \in \mathcal{B}(\underline{B}')} \langle x, x'\rangle$, with the supremum attained as an adherent point. | `mcone_norm_le_pairing_ub`, `mcone_test_pairing_adherent` — `theories/mcones/mcone_cat.v` (`Section Proposition311`) |
| Def 3.16 (§3.4.1) | The *measure cone* $\mathsf{FMeas}(X)$ of finite measures on $X$, with tests $\widetilde{U} : \mu \mapsto \mu(U)$ for $U \in \sigma_X$. | `fmeas`, the `FMeas` HB instance — `theories/mcones/fmeas.v` |
| Def 3.7 | A *path* of arity $X$ is a bounded map $\gamma : X \to \underline{C}$ whose pointwise test pairings are jointly measurable. | `path_car` — `theories/mcones/path.v`; `path_int_exists` lives in `theories/icones/examples_icone.v` (see § 4 below) |
| Cat 3 | $\mathbf{MCones}$ is a category. | `MCones` (above) — `theories/mcones/mcone_cat.v` |

The Rocq encoding faithfully treats `ARCAT` as a parameter (`MeasSubcat R`)
just as the paper does (paper §3, around `content.tex:1029`).

> **Path note.** The original table cited `path_int_exists` as living in
> `theories/mcones/path.v`, but it is in fact stated as the
> `isICone`-witness `path_int_exists` in `theories/icones/examples_icone.v`
> (path is integrable iff its codomain is — paper Thm 4.12). Fixed in
> this revision; the underlying path data type `path_car` does live in
> `path.v`.

### `ARCAT` (`MeasSubcat`)

The arity category $\mathbf{Ar}$ is a small full subcategory of $\mathbf{Meas}$ (measurable spaces and measurable functions) closed under cartesian products, containing the one-point terminal object $0$, and all of whose objects are non-empty. Packaging it as a record `MeasSubcat R` makes the whole §3+ tower parametric in the chosen subcategory.

> **Paper — §3** (arXiv 2212.02371, `content.tex:1029`). Let $\mathbf{Ar}$ be a *small* full subcategory of $\mathbf{Meas}$ (the category of measurable spaces and measurable functions) which is closed under cartesian products and contains the terminal object $0$ which is the one point measurable space. We also assume all the objects of $\mathbf{Ar}$ to be non-empty measurable spaces.

```coq
(* theories/mcones/ar.v *)
Record MeasSubcat (R : realType) : Type := MkMeasSubcat {
  ar_obj     : Type;
  ar_disp    : ar_obj -> measure_display;
  ar_carrier : forall X : ar_obj, measurableType (ar_disp X);
  ar_point   : forall X : ar_obj, ar_carrier X;
  ar_zero    : ar_obj;
  ar_zero_singleton :
    forall x y : ar_carrier ar_zero, x = y;
  ar_prod         : ar_obj -> ar_obj -> ar_obj;
  ar_prod_disp_eq : forall X Y, ar_disp (ar_prod X Y) =
                    measure_prod_display (ar_disp X, ar_disp Y);
  ar_prod_carrier_eq :
    forall X Y, ar_carrier (ar_prod X Y) =
                (ar_carrier X * ar_carrier Y)%type :> Type;
  ar_prod_uncast_meas :
    forall X Y, measurable_fun setT
      (fun p : ar_carrier (ar_prod X Y) =>
         eq_rect _ (fun T => T) p _ (ar_prod_carrier_eq X Y));
  ar_prod_cast_meas :
    forall X Y, measurable_fun setT
      (fun p : (ar_carrier X * ar_carrier Y)%type =>
         eq_rect_r (fun T => T) p (ar_prod_carrier_eq X Y));
}.
```

### Def 3.2 / 3.6 (`isMCone` / `MCone`)

A *measurable cone* is a cone $\underline{C}$ equipped with a *measurability structure* $\mathcal{M}=(\mathcal{M}_X)_{X\in\mathbf{Ar}}$: an $\mathbf{Ar}$-indexed family of test sets $\mathcal{M}_X\subseteq(\underline{C}')^X$ satisfying measurability (Msmeas), compatibility with reindexing (Mscomp), separation (Mssep) and the norm formula (Msnorm). The `isMCone` mixin bundles this structure onto a `Cone`.

> **Paper — Definition 3.2** (arXiv 2212.02371, `def:meas-structure`). A *measurability structure* on a cone $P$ is a family $\mathcal{M}=(\mathcal{M}_X)_{X\in\mathbf{Ar}}$ with $\mathcal{M}_X\subseteq(P')^{X}$ (where $P'=(P\multimap\perp)$ is the dual of the cone $P$) satisfying the four next conditions (Msmeas), (Mscomp), (Mssep) and (Msnorm). When $X=0$ we consider $m\in\mathcal{M}_X$ as an element of $P'$. $$\text{(Msmeas)}\quad \text{for each } m\in\mathcal{M}_X,\ x\in\mathcal{B}P,\quad \boldsymbol\lambda r\in X\cdot m(r,x)\in\mathbf{Meas}(X,[0,1]).$$ $$\text{(Mscomp)}\quad \text{for each } m\in\mathcal{M}_X,\ \phi\in\mathbf{Ar}(Y,X),\quad \boldsymbol\lambda (s,x)\in(Y\times P)\cdot m(\phi(s),x)=m\mathrel{\circ}(\phi\times P)\in\mathcal{M}_Y.$$ $$\text{(Mssep)}\quad \text{if } x_1,x_2\in P \text{ satisfy } \forall m\in\mathcal{M}_0\ m(x_1)=m(x_2)\ \text{then}\ x_1=x_2.$$ $$\text{(Msnorm)}\quad \forall x\in P\quad \lVert x\rVert=\sup\Big\{\tfrac{m(x)}{\lVert m\rVert}\mid m\in\mathcal{M}_0\text{ and }m\neq 0\Big\}.$$

> **Paper — Definition 3.6** (arXiv 2212.02371). A *measurable cone* is a pair $C=(\underline{C},\mathcal{M}^{C})$ where $\underline{C}$ is a cone and $\mathcal{M}^{C}$ is a measurability structure on $\underline{C}$.

> **Difference.** The paper's norm axiom (Msnorm) is an *attained* supremum over all non-zero tests at arity $0$; the formalization records instead the equivalent $\varepsilon$-approximation form of Remark 3.3 (`mcone_M_norm`): for every $x\neq 0$ and $\varepsilon>0$ some test $m$ satisfies $\lVert x\rVert\le m(x)+\varepsilon$. *Why:* the supremum need not be attained, so it is expressed as adherence rather than a maximum. The measurability axiom (Msmeas) is carried by the `test_of` type of tests, not spelled as a separate mixin field.

```coq
(* theories/mcones/mcone.v *)
HB.mixin Record isMCone (R : realType) (Ar : MeasSubcat R) C of Cone R C := {
  mcone_M : forall X : ar_obj Ar, set (test_of Ar X C);
  mcone_M_comp :
    forall (Y X : ar_obj Ar) (φ : ar_hom Ar Y X) (m : test_of Ar X C),
      mcone_M X m -> mcone_M Y (test_reindex φ m);
  mcone_M_sep :
    forall x1 x2 : C,
      (forall m : test_of Ar (ar_zero Ar) C,
        mcone_M (ar_zero Ar) m ->
        test_fun m (ar_zero_pt Ar) x1 = test_fun m (ar_zero_pt Ar) x2) ->
      x1 = x2;
  mcone_M_norm :
    forall (x : C) (eps : R),
      x <> precone_zero -> 0 < eps ->
      exists m : test_of Ar (ar_zero Ar) C,
        mcone_M (ar_zero Ar) m /\
        cone_norm x <= test_fun m (ar_zero_pt Ar) x + eps;
}.

HB.structure Definition MCone (R : realType) (Ar : MeasSubcat R) :=
  { C of Cone R C & isMCone R Ar C }.
```

### Def 3.13 (`mcones_hom`, `mcones_comp`, `MCones`)

The category $\mathbf{MCones}$ has measurable cones as objects; a morphism $B\to C$ is a $\mathbf{Cones}$-morphism $f$ that maps every measurable path in $B$ to a measurable path in $C$. The `mcones_hom` record pairs a `cones_hom` with the path-preservation witness `mcones_hom_pres_path`.

> **Paper — Definition 3.13** (arXiv 2212.02371). The category $\mathbf{MCones}$ has measurable cones as objects and an element of $\mathbf{MCones}(B,C)$ is an $f\in\mathbf{Cones}(\underline{B},\underline{C})$ such that for each $X\in\mathbf{Ar}$ and each measurable path $\beta:X\to\underline{B}$ the function $f\mathrel{\circ}\beta$ is a measurable path. Equivalently $$\forall Y\in\mathbf{Ar}\ \forall m\in\mathcal{M}^{C}_Y\quad\boldsymbol\lambda (s,r)\in{X\times Y}\cdot m(s,f(\beta(r)))\text{ is measurable.}$$

```coq
(* theories/mcones/mcone_cat.v — Section MConesHom,
   Variables (R : realType) (Ar : MeasSubcat R), B C : MCone.type Ar *)
Record mcones_hom : Type := MkMConesHom {
  mcones_hom_cones :> cones_hom B C;
  mcones_hom_pres_path :
    forall (X : ar_obj Ar) (γ : ar_carrier Ar X -> B),
      is_measurable_path (Ar:=Ar) (C:=B) γ ->
      is_measurable_path
        (Ar:=Ar) (C:=C)
        (fun r => cones_hom_fun mcones_hom_cones (γ r));
}.

Definition mcones_comp
    (g : mcones_hom Ar B C) (f : mcones_hom Ar A B) : mcones_hom Ar A C :=
  MkMConesHom
    (cones_comp (mcones_hom_cones g) (mcones_hom_cones f))
    (mcones_comp_pres_path g f).
```

### Prop 3.11 (`mcone_norm_le_pairing_ub`, `mcone_test_pairing_adherent`)

The dual-norm characterisation, mechanised in two constructive directions: `mcone_test_pairing_adherent` gives the $\le$ direction — for $x \ne 0$ and $\varepsilon > 0$, a test pairing lies within $\varepsilon$ of $\lVert x\rVert$ — and `mcone_norm_le_pairing_ub` gives that any upper bound $M$ of the pairing set dominates $\lVert x\rVert$.

> **Paper — Proposition 3.11** (arXiv 2212.02371, `th:norm-dual`). Let $B$ be a measurable cone and let $x \in \lvert B\rvert$. Then $\lVert x\rVert = \sup_{x' \in \mathbf{B}(\lvert B\rvert^{*})} \langle x, x'\rangle$, the supremum ranging over the closed unit ball $\mathbf{B}(\lvert B\rvert^{*})$ of the dual measurable cone $\lvert B\rvert^{*}$.

> **Difference.** The paper states the norm as an *attained* supremum; the formalization splits it into the two constructive lemmas below — `mcone_norm_le_pairing_ub` (any upper bound $M$ of the pairing set dominates $\lVert x\rVert$) and `mcone_test_pairing_adherent` (for $\varepsilon > 0$, a pairing lies within $\varepsilon$ of $\lVert x\rVert$). *Why:* the supremum need not be attained, so the $\le$ direction is expressed as adherence — an $\varepsilon$-approximation — rather than a maximum.

```coq
(* theories/mcones/mcone_cat.v — Section Proposition311,
   Variables (R : realType) (Ar : MeasSubcat R) (B : MCone.type Ar) *)
Lemma mcone_test_pairing_adherent (x : B) (eps : R) :
  x <> precone_zero -> 0 < eps ->
  exists2 y, mcone_test_pairing_set x y & cone_norm x <= y + eps.

Lemma mcone_norm_le_pairing_ub (x : B) (M : R) :
  x <> precone_zero ->
  ubound (mcone_test_pairing_set x) M -> cone_norm x <= M.
```

### Def 3.16 / §3.4.1 (`fmeas`, `FMeas`)

The measure cone $\mathsf{FMeas}(X)$ of finite measures on a measurable space $X$ carries, for each $Y\in\mathbf{Ar}$, the measurability structure $\mathcal{M}_Y=\{\widetilde{U}\mid U\in\sigma_X\}$ where $\widetilde{U}(s,\mu)=\mu(U)$. The `fmeas` record is the carrier (a finite, canonical measure); the `isMCone` instance installs the test family.

> **Paper — §3.4.1 "The measurable cone of measures"** (arXiv 2212.02371, `content.tex:1340`). For all $Y\in\mathbf{Ar}$ and all $U\in\sigma_X$ define $\widetilde{U}:Y\times\underline{\mathsf{FMeas}(X)}\to\mathbb{R}_{\geq 0}$ by $\widetilde{U}(s,\mu)=\mu(U)$. Then $\mathcal{M}_Y=\{\widetilde{U}\mid U\in\sigma_X\}$, and $\mathsf{FMeas}(X)=(\underline{\mathsf{FMeas}(X)},(\mathcal{M}_Y)_{Y\in\mathbf{Ar}})$ is a measurable cone.

> **Difference.** Remark 3.16 (`rk:measure-cone-two-ms`) offers a second, coarser test family $\mathcal{M}_Y=\{\widetilde{W}\mid W\in\sigma_{Y\times X}\}$ inducing the *same* measurable paths; the formalization commits to the point-tested family $\widetilde{U}$ of §3.4.1 above.

```coq
(* theories/mcones/fmeas.v — Variables R X *)
Record fmeas : Type := MkFmeas {
  fmeas_mu        :> {measure set X -> \bar R};
  fmeas_fin       : fmeas_finP fmeas_mu;
  fmeas_canonical : fmeas_canon fmeas_mu;
}.

HB.instance Definition _ :=
  @isMCone.Build R Ar (fmeas R X)
    fmeas_mcone_M
    fmeas_mcone_M_comp
    fmeas_mcone_M_sep
    fmeas_mcone_M_norm.
```

### Def 3.7 (`path_car`)

A *measurable path* of arity $X$ is a bounded function $\gamma:X\to\underline{C}$ whose composition with every test $m\in\mathcal{M}^{C}_Y$ is jointly measurable on $Y\times X$. The `path_car` record pairs the underlying map with the `is_measurable_path` witness.

> **Paper — Definition 3.7** (arXiv 2212.02371). Let $X\in\mathbf{Ar}$ and let $C$ be a measurable cone. A *(measurable) path* of arity $X$ is a function $\gamma:X\to\underline{C}$ which is bounded and such that, for each $Y\in\mathbf{Ar}$ and $m\in\mathcal{M}^{C}_{Y}$, the function $\boldsymbol\lambda (s,r)\in{Y\times X}\cdot m(s,\gamma(r)): {Y\times X}\to\mathbb{R}_{\geq 0}$ is measurable. We use $\underline{\mathsf{Path}(X,C)}$ for the set of measurable paths of arity $X$ of the measurable cone $C$.

```coq
(* theories/mcones/path.v — Section PathCarrier,
   Variables (R : realType) (Ar : MeasSubcat R) (X : ar_obj Ar)
             (B : MCone.type Ar) *)
Record path_car : Type := MkPath {
  path_fun     :> ar_carrier Ar X -> B;
  path_is_path : is_measurable_path (Ar:=Ar) (C:=B) (X:=X) path_fun;
}.
```

---

## Paper § 4 — Integrable cones (ICones)

The paper makes a cone *integrable* by demanding that every probability
measure / path can be Pettis-integrated against the cone. The formalisation
builds the full HB tower `Precone → Cone → MCone → ICone`.

| Paper | English statement | Rocq |
|---|---|---|
| Def 4.1 | An *integrable cone* (`ICone`) is a measurable cone in which every path admits a Pettis integral with respect to every (sub-)probability measure. | `ICone.type` (via `isICone` mixin) — `theories/icones/icone.v` |
| Def 4.2 | The Pettis integral $\int_\mu \eta \in C$ is the unique element pairing with every test $t$ as $\int \langle t, \eta(r)\rangle\,d\mu$. | `icone_integral`, `icone_integral_eqP` (uniqueness) — `theories/icones/icone.v` |
| Lem 4.7 | The integration operator $\mathcal{I}^{B}_X$ is bilinear (separately linear in the path and the measure), continuous and measurable. | `icone_integral_*` family + `bilin.v` — `theories/icones/icone_integral.v`, `theories/homs/bilin.v` |
| Thm 4.12 | The cone of paths $\mathsf{Path}(X,B)$ into an integrable cone is itself an `ICone`. | the anonymous `isICone` instance built from `path_int_exists` — `theories/icones/examples_icone.v` |
| Thm 4.5 | $\mathsf{FMeas}(X)$ is integrable; the unit cone $1=\perp$ likewise. | `FMeas` is an `ICone`; the `isICone` instance on `cone_one_car Ar` — `theories/icones/examples_icone.v` |
| Cat 4 | The category $\mathbf{ICones}$ has integrable cones and $\mathbf{MCones}$-morphisms preserving the integral. | `icones_hom`, `icones_comp`, `ICones` — `theories/icones/icone_cat.v` |
| Thm 4.15 (Fubini) | The Fubini / iterated-integral identity for paths over a product space. | `fubini_iter_fun_X` — `theories/icones/fubini.v` |
| Thm 4.18 | $\mathbf{ICones}$ is well-powered (and $1$ is a separator and coseparator). | `icones_well_powered` (full proof, no stub) — `theories/icones/representable.v` |
| Thm 4.19 | $\mathbf{ICones}$ is complete with $1$ a coseparator; therefore every limit-preserving functor $\mathbf{ICones}\to\mathcal{C}$ has a left adjoint (by SAFT). | The completeness data (products, equalisers, the coseparator) is in `icone_cat.v`; the bespoke **SAFT engine** is `representable.v` (`wi_obj`, `wi_med`, `is_icones_left_adjoint`) — see *Beyond the paper* below |

### Def 4.3 (`isICone`, `ICone`)

A measurable cone is *integrable* when, for every arity $X\in\mathbf{Ar}$, every measurable path $\beta:X\to\underline{B}$ admits an integral over every finite measure $\mu\in\underline{\mathsf{FMeas}(X)}$. The `isICone` mixin bundles this existence witness onto an `MCone`.

> **Paper — Definition 4.3** (arXiv 2212.02371, `def:integral-in-cone`). A measurable cone is *integrable* if, for all $X\in\mathbf{Ar}$, each $\beta\in\underline{\mathsf{Path}(X,B)}$ has an integral in $\underline{B}$ over each measure $\mu\in\underline{\mathsf{FMeas}(X)}$. When this is the case we use $\mathcal{I}^{B}_X$ for the uniquely defined function $\underline{\mathsf{Path}(X,B)}\times\underline{\mathsf{FMeas}(X)}\to\underline{B}$ such that $\mathcal{I}^{B}_X(\beta,\mu)=\int\beta(r)\mu(dr)$.

```coq
(* theories/icones/icone.v *)
HB.mixin Record isICone (R : realType) (Ar : MeasSubcat R) B
  of MCone R Ar B := {
  icone_exists :
    forall (X : ar_obj Ar)
           (β : ar_carrier Ar X -> B),
      is_measurable_path β ->
      forall µ : fmeas R (ar_carrier Ar X),
        is_path_integrable β µ;
}.

HB.structure Definition ICone (R : realType) (Ar : MeasSubcat R) :=
  { B of isICone R Ar B & MCone R Ar B }.
```

### Def 4.1 (`icone_integral`, `icone_integral_eqP`)

The integral $\mathcal{I}^{B}_X(\beta,\mu)\in\underline{B}$ of a measurable path $\beta$ over a finite measure $\mu$ is the element $x$ pairing correctly with every arity-$0$ test $m$, i.e. $m(x)=\int m(\beta(r))\,\mu(dr)$; by separation it is unique. In Rocq, `icone_integral` names the value, `icone_integralP` its defining equation, and `icone_integral_eqP` its uniqueness.

> **Paper — Definition 4.1** (arXiv 2212.02371). Let $B$ be a measurable cone, $X\in\mathbf{Ar}$, $\beta\in\underline{\mathsf{Path}(X,B)}$ and $\mu\in\underline{\mathsf{FMeas}(X)}$. An *integral of $\beta$ over $\mu$* is an element $x$ of $\underline{B}$ such that, for all $m\in\mathcal{M}^{B}_0$, one has $$m(x)=\int m(\beta(r))\mu(dr)\,.$$

```coq
(* theories/icones/icone.v — Section ICOneIntegral,
   Variables R Ar B X β Hβ µ *)

Definition icone_integral : B :=
  path_integral (icone_exists X β Hβ µ).

Lemma icone_integralP : path_integral_eq β µ icone_integral.

Lemma icone_integral_eqP (x : B) :
  path_integral_eq β µ x -> x = icone_integral.
```

### Lem 4.7 (`icone_integral_*` family + `bilin.v`)

The integration operator $\mathcal{I}^{B}_X$ is bilinear, continuous and measurable. Bilinearity is captured by four equations — additivity and scalar homogeneity separately in the path $\beta$ and in the measure $\mu$ — while continuity/measurability are the chain-monotonicity and joint-measurability companions consumed downstream.

> **Paper — Lemma 4.7** (arXiv 2212.02371, `lemma:int-mesurable`). For each $X\in\mathbf{Ar}$, the map $\mathcal{I}^{B}_X$ is bilinear, continuous and measurable. This means that $\mathcal{I}^{B}_X:\underline{\mathsf{Path}(X,B)}\mathrel{\&}\underline{\mathsf{FMeas}(X)}\to\underline{B}$ is continuous, separately linear in each of its two arguments and that for each $Y\in\mathbf{Ar}$, $\eta\in\underline{\mathsf{Path}(Y,\mathsf{Path}(X,B))}$ and $\kappa\in\underline{\mathsf{Path}(Y,\mathsf{FMeas}(X))}$, the function $\beta=\mathcal{I}^{B}_X\mathrel{\circ}\langle \eta,\kappa\rangle:Y\to\underline{B}$ is a measurable path.

> **Difference.** The single paper lemma is unbundled into named equations: separate linearity is the four `icone_integral_addB` / `icone_integral_scaleB` (in $\beta$) and `icone_integral_addmu` / `icone_integral_scalemu` (in $\mu$), while continuity and measurability are the `icone_integral_chain_le` and `icone_integral_joint_measurable` companions. *Why:* each fact is consumed independently downstream (and the bilinear packaging lives in `theories/homs/bilin.v`), so it is more convenient to state them one at a time than as one conjunction.

```coq
(* theories/icones/icone_integral.v — Section variables R Ar B X β Hβ µ *)

Lemma icone_integral_addB
  (β1 β2 : ar_carrier Ar X -> B)
  (Hβ1 : is_measurable_path β1) (Hβ2 : is_measurable_path β2)
  (Hβ12 : is_measurable_path (fun r => precone_add (β1 r) (β2 r))) :
  icone_integral (fun r => precone_add (β1 r) (β2 r)) Hβ12 µ =
  precone_add (icone_integral β1 Hβ1 µ) (icone_integral β2 Hβ2 µ).

Lemma icone_integral_scaleB
  (r : {nonneg R}) (β : ar_carrier Ar X -> B)
  (Hβ : is_measurable_path β)
  (Hrβ : is_measurable_path (fun u => precone_scale r (β u))) :
  icone_integral (fun u => precone_scale r (β u)) Hrβ µ =
  precone_scale r (icone_integral β Hβ µ).

Lemma icone_integral_addmu (µ1 µ2 : fmeas R (ar_carrier Ar X)) :
  icone_integral β Hβ (fmeas_add µ1 µ2) =
  precone_add (icone_integral β Hβ µ1) (icone_integral β Hβ µ2).

Lemma icone_integral_scalemu
  (r : {nonneg R}) (µ : fmeas R (ar_carrier Ar X)) :
  icone_integral β Hβ (fmeas_scale r µ) =
  precone_scale r (icone_integral β Hβ µ).

Lemma icone_integral_test_pettis (Z : ar_obj Ar) (* ... *).
Lemma icone_integral_chain_le : (* ... *).
Lemma icone_integral_joint_measurable : (* ... *).
```

### Thm 4.5 / 4.12 (`path_int_exists`, `FMeas`/unit `isICone` instances)

The two archetypal integrable cones are exhibited: the cone of finite measures $\mathsf{FMeas}(X)$ (Thm 4.5) and, for any integrable $B$, the cone of measurable paths $\mathsf{Path}(X,B)$ (Thm 4.12), whose integral is computed pointwise. The same file also installs the `isICone` instance on the unit cone $1=\perp$.

> **Paper — Theorem 4.5** (arXiv 2212.02371). For each measurable space $X$, the measurable cone $\mathsf{FMeas}(X)$ is integrable.

> **Paper — Theorem 4.12** (arXiv 2212.02371). For each $X\in\mathbf{Ar}$ and each integrable cone $B$, the measurable cone $\mathsf{Path}(X,B)$ is integrable.

```coq
(* theories/icones/examples_icone.v *)

Lemma path_int_exists
    (Y' : ar_obj Ar)
    (η : ar_carrier Ar Y' -> P)
    (Hη : is_measurable_path η)
    (ν : fmeas R (ar_carrier Ar Y')) :
  is_path_integrable η ν.

HB.instance Definition _ : isICone R Ar P :=
  isICone.Build R Ar P (@path_int_exists).

HB.instance Definition _ :=
  @isICone.Build R Ar (cone_one_car Ar) (* ... witness ... *).

HB.instance Definition _ :=
  @isICone.Build R Ar (fmeas R (ar_carrier Ar X)) (* ... witness ... *).
```

### Def 4.10 (`icones_hom`, `icones_comp`, `ICones`)

The category $\mathbf{ICones}$ has integrable cones as objects; a morphism $B\to C$ is an $\mathbf{MCones}$-morphism $f$ that *preserves integrals*: $f(\int\beta(r)\mu(dr))=\int f(\beta(r))\mu(dr)$. The `icones_hom` record pairs an `mcones_hom` with the integral-preservation witness `icones_hom_pres_int`.

> **Paper — Definition 4.10** (arXiv 2212.02371, `def:icones-category`). The category $\mathbf{ICones}$ has integrable cones as objects and an element of $\mathbf{ICones}(B,C)$ is an $f\in\mathbf{MCones}(B,C)$ such that, for all $X\in\mathbf{Ar}$ and all $\beta\in\underline{\mathsf{Path}(X,B)}$ and $\mu\in\underline{\mathsf{FMeas}(X)}$ one has $$f\Big(\int\beta(r)\mu(dr)\Big)=\int f(\beta(r))\mu(dr)\,.$$ This property of $f$ will be called *integral preservation* and when it holds we often simply say that $f$ is *integrable*.

```coq
(* theories/icones/icone_cat.v — Section IConesHom,
   Variables (R : realType) (Ar : MeasSubcat R), B C : ICone.type Ar *)

Record icones_hom : Type := MkIConesHom {
  icones_hom_mcones :> mcones_hom Ar B C;
  icones_hom_pres_int :
    forall (X : ar_obj Ar) (β : ar_carrier Ar X -> B)
           (Hβ : is_measurable_path β)
           (µ : fmeas R (ar_carrier Ar X)),
      cones_hom_fun (mcones_hom_cones icones_hom_mcones)
                    (icone_integral β Hβ µ) =
      icone_integral
        (fun r => cones_hom_fun (mcones_hom_cones icones_hom_mcones) (β r))
        (mcones_hom_pres_path icones_hom_mcones X β Hβ) µ;
}.

Definition icones_id : icones_hom Ar B B :=
  MkIConesHom (mcones_id Ar B) icones_id_pres_int.

Definition icones_comp
    (g : icones_hom Ar B C) (f : icones_hom Ar A B) : icones_hom Ar A C :=
  MkIConesHom
    (mcones_comp (icones_hom_mcones g) (icones_hom_mcones f))
    (icones_comp_pres_int g f).
```

### Thm 4.15 Fubini (`fubini_iter_fun_X`)

The Fubini theorem for cones: iterated integration of a path of paths equals integration of the flattened path against the product measure. The Rocq development builds the inner-integral function $x\mapsto\int_y\beta(x,y)\,d\nu$, bounds its norm, and shows it is itself a measurable path — the ingredients of the iterated-integral identity.

> **Paper — Theorem 4.15** (arXiv 2212.02371, `th:paths-Fubini`). Let $X,Y\in\mathbf{Ar}$, $\eta\in\underline{\mathsf{Path}(X,\mathsf{Path}(Y,B))}$, $\mu\in\underline{\mathsf{FMeas}(X)}$ and $\nu\in\underline{\mathsf{FMeas}(Y)}$. We have $$\int_Y\Big(\int_X\eta(r)\mu(dr)\Big)(s)\nu(ds) =\int_{X\times Y}\mathsf{fl}(\eta)(t)\,(\mu\times\nu)(dt)$$

> **Difference.** The excerpt shown is the supporting apparatus rather than the final identity: `fubini_iter_fun_X` is the inner integral $x\mapsto\int_y\beta(x,y)\,d\nu$, with `fubini_iter_fun_X_norm_le` bounding its norm and `fubini_iter_fun_X_is_path` proving it is a measurable path. These are the lemmas the iterated-integral equation of Theorem 4.15 is assembled from in `fubini.v`.

```coq
(* theories/icones/fubini.v — Variables
   R Ar B (X Y : ar_obj Ar)
   (β : ar_carrier Ar X * ar_carrier Ar Y -> B)
   (ν : fmeas R (ar_carrier Ar Y)) *)

Definition fubini_iter_fun_X (x : ar_carrier Ar X) : B :=
  icone_integral (fun y => β (x, y)) (Hβ x) ν.

Lemma fubini_iter_fun_X_norm_le (Mβ : R) :
  (forall p, cone_norm (β p) <= Mβ) ->
  forall x, cone_norm (fubini_iter_fun_X x) <= Mβ * fmeas_norm ν.

Lemma fubini_iter_fun_X_is_path (Mβ : R)
  (HMβ : forall p, cone_norm (β p) <= Mβ)
  (Hjoint : (* joint test-measurability of β *)) :
  is_measurable_path fubini_iter_fun_X.
```

### Thm 4.18 (`icones_well_powered`, `SubobjClassifier`, `icones_subobject_classP`)

In $\mathbf{ICones}$ the unit cone $1$ is both a separator and a coseparator, and the category is well-powered. The formalization discharges well-poweredness by exhibiting a small classifying `Type` (`SubobjClassifier`) into which subobjects inject up to iso (`icones_subobject_classP`) — the property the special adjoint functor theorem then consumes.

> **Paper — Theorem 4.18** (arXiv 2212.02371, `th:icones-conditions-saft`). In the category $\mathbf{ICones}$ the object $1$ is a coseparator and a separator and $\mathbf{ICones}$ is well-powered.

> **Difference.** This entry mechanises only the *well-powered* conjunct — recast as the existence of a small classifying `Type` `SubobjClassifier` that identifies subobjects up to iso (`icones_subobject_classP`). This is the exact input the special adjoint functor theorem needs; the separator/coseparator role of $1$ is handled where SAFT is applied (see *Beyond the paper* below).

```coq
(* theories/icones/representable.v — Section Classifier,
   Variables (R : realType) (Ar : MeasSubcat R), B : ICone.type Ar *)

Record SubobjClassifier : Type := MkClassifier {
  cls_S    : set B;
  cls_add  : B -> B -> B;
  cls_scl  : {nonneg R} -> B -> B;
  cls_zer  : B;
  cls_nrm  : B -> R;
  cls_M    : forall X : ar_obj Ar,
               set (ar_carrier Ar X -> B -> R);
}.

Lemma icones_subobject_classP (D1 D2 : icones_subobject B) :
  icones_subobject_class D1 = icones_subobject_class D2 ->
  subobject_equiv D1 D2.

Theorem icones_well_powered :
  exists cls : icones_subobject B -> SubobjClassifier B,
    forall D1 D2 : icones_subobject B,
      cls D1 = cls D2 -> subobject_equiv D1 D2.
Proof. by exists icones_subobject_class; exact: icones_subobject_classP. Qed.
```

(The SAFT engine — `pb_med`, `wi_obj`, `wi_med`, `wi_factors_each`,
`wi_incl_inj`, `is_icones_left_adjoint` — is collected under
*Beyond the paper* below.)

---

## Paper § 5 — Internal hom, tensor, and SMCC

| Paper | English statement | Rocq |
|---|---|---|
| Lem 5.4 / Def 5.7 | The internal hom $C\multimap D$ carrier (the integrable cone of $\mathbf{ICones}$-morphisms $C\to D$); its action $(h\multimap g):(C_1\multimap D_1)\to(C_2\multimap D_2)$ by $(h\multimap g)(f)=g\circ f\circ h$. | `linhom_car`, `linhom_postc`, `linhom_prec`, `linhom_map_fun` — `theories/homs/linhom.v` |
| Prop 5.8 | The internal-hom action $h\multimap g$ lifts to an $\mathbf{ICones}$ morphism. | `linhom_map_icones` — `theories/homs/linhom_functor.v` |
| Thm 5.9 | The functor $C\multimap{-}$ preserves all limits (hence has a left adjoint). | `limpl_preserves_prod`, `limpl_preserves_limits` — `theories/homs/limpl_continuous.v` |
| Thm 5.12 | The currying isomorphism $(B\otimes C)\multimap D\;\simeq\;B\multimap(C\multimap D)$. | `tensor_hom_iso` — `theories/homs/tensor_iso.v` |
| Thm 5.13 | Norm identity for pure tensors: $\lVert x\otimes y\rVert=\lVert x\rVert\,\lVert y\rVert$. | `tensor_norm_le` ($\le$) + the $\ge$ direction via Prop 3.11 — `theories/homs/tensor.v` / `tensor_iso.v` |
| Prop 5.14 | A morphism out of an iterated tensor is determined on pure tensors $x\otimes y$. | `tensor_ext`, `tensor_ext3`, `tensor_ext4` — `theories/homs/tensor.v`, `theories/homs/smcc.v` |
| Thm 5.15 | $(\mathbf{ICones},\otimes,1)$ is a symmetric monoidal closed category. | `ICones_SMCC`, `ICones_smcc` — `theories/homs/smcc.v` |
| Rem 5.1 | The tensor object is given by SAFT, without an explicit carrier. | The paper's invocation of SAFT is *mechanised* concretely in `representable.v` + `tensor_construct.v` — see *Beyond the paper* below |

### Lem 5.4 / Def 5.7 (`linhom_car`, `linhom_postc`, `linhom_prec`, `linhom_map_fun`)

The internal hom $C\multimap D$ is the measurable cone of linear, continuous, measurable, integral-preserving morphisms $C\to D$; the paper shows it is itself integrable (Lem 5.4). Its bifunctorial action on morphisms $h\in\mathbf{ICones}(C_2,C_1)$ and $g\in\mathbf{ICones}(D_1,D_2)$ sends $f\mapsto g\circ f\circ h$ (Def 5.7), contravariant in the domain and covariant in the codomain.

> **Paper — Lemma 5.4** (arXiv 2212.02371). The measurable cone $C\multimap D$ is integrable.

> **Paper — Definition 5.7** (arXiv 2212.02371). Let $g\in\mathbf{ICones}(D_1,D_2)$ and $h\in\mathbf{ICones}(C_2,C_1)$. The function $h\multimap g:\underline{C_1\multimap D_1}\to\underline{C_2\multimap D_2}$ is defined by $(h\multimap g)(f)=g\,f\,h$.

```coq
(* theories/homs/linhom.v — Section LinhomCar,
   Variables (R : realType) (Ar : MeasSubcat R), C D : ICone.type Ar *)
Record linhom_car : Type := MkLinhom {
  linhom_pre_of :> linhom_pre Ar C D;
  linhom_pres_int :
    forall (X : ar_obj Ar) (β : ar_carrier Ar X -> C)
           (Hβ : is_measurable_path β)
           (µ : fmeas R (ar_carrier Ar X)),
      linhom_pre_fun linhom_pre_of (icone_integral β Hβ µ) =
      icone_integral
        (fun r => linhom_pre_fun linhom_pre_of (β r))
        (linhom_pre_pres_path linhom_pre_of X β Hβ) µ;
}.

(* postcomposition / precomposition / object map of ⊸ *)
Definition linhom_postc : linhom_car Ar C D2 :=
  MkLinhom postc_pre postc_pres_int.
Definition linhom_prec : linhom_car Ar C2 D :=
  MkLinhom prec_pre prec_pres_int.

Definition linhom_map_fun
    (C1 C2 D1 D2 : ICone.type Ar)
    (h : icones_hom Ar C2 C1) (g : icones_hom Ar D1 D2)
    (f : linhom_car Ar C1 D1) : linhom_car Ar C2 D2 :=
  linhom_prec h (linhom_postc g f).
```

### Prop 5.8 (`linhom_map_icones`)

The bifunctorial action $h\multimap g$ is not merely a function on carriers: it is a genuine $\mathbf{ICones}$ morphism, which makes $\multimap$ a functor $\mathbf{ICones}^{\mathrm{op}}\times\mathbf{ICones}\to\mathbf{ICones}$.

> **Paper — Proposition 5.8** (arXiv 2212.02371). If $g\in\mathbf{ICones}(D_1,D_2)$ and $h\in\mathbf{ICones}(C_2,C_1)$ then $h\multimap g\in\mathbf{ICones}(C_1\multimap D_1,C_2\multimap D_2)$.

```coq
(* theories/homs/linhom_functor.v *)
Definition linhom_map_icones : icones_hom Ar (linhom_car Ar C1 D1)
                                            (linhom_car Ar C2 D2) :=
  MkIConesHom linhom_map_mcones linhom_map_pres_int.
```

### Thm 5.9 (`limpl_preserves_prod`, `limpl_preserves_limits`)

For each integrable cone $C$, the internal-hom functor $C\multimap{-}$ preserves all limits: it turns the product $\mathbin{\&}_i D_i$ into $\mathbin{\&}_i(C\multimap D_i)$ and respects equalisers. By the adjoint functor theorem for $\mathbf{ICones}$ this yields the paper's left adjoint (the tensor $-\otimes C$).

> **Paper — Theorem 5.9** (arXiv 2212.02371, `th:limpl-has-left-adj`). For each integrable cone $C$, the functor $C\multimap{-}$ has a left adjoint.

> **Difference.** The paper concludes existence of a left adjoint from the special adjoint functor theorem (Thm 4.19), whose hypothesis is that $C\multimap{-}$ *preserves all limits*. The formalization mechanises exactly that limit-preservation hypothesis — `limpl_preserves_limits`, decomposed into products (`limpl_preserves_prod`) and equalisers — as the load-bearing content; the tensor left adjoint itself is then built concretely in *Beyond the paper*.

```coq
(* theories/homs/limpl_continuous.v *)
Definition limpl_preserves_prod :
  icones_iso Ar (linhom_car Ar C Dprod) Lprod :=
  icones_iso_of_cancel limpl_prod_fwd limpl_prod_inv_icones
    limpl_prod_invK limpl_prod_fwdK.

Record limpl_continuous : Prop := MkLimplContinuous {
  lc_prod :
    forall (I : Type) (D : I -> ICone.type Ar),
      { iso : icones_iso Ar (linhom_car Ar C (icones_prod D))
                            (icones_prod (fun i => linhom_car Ar C (D i)))
      | iso_fwd iso = limpl_prod_fwd C D };
  lc_eq_equ : (* equalisers half *) _;
  lc_eq_med : (* mediator with factor + uniqueness *) _;
}.

Theorem limpl_preserves_limits : limpl_continuous.
```

### Thm 5.12 (`tensor_hom_iso`)

The adjunction bijection $\Phi_{B,C,D}:\mathbf{ICones}(B\otimes C,D)\to\mathbf{ICones}(B,C\multimap D)$ upgrades to a full isomorphism of integrable cones $(B\otimes C)\multimap D\;\simeq\;B\multimap(C\multimap D)$: this is the closedness of the monoidal structure.

> **Paper — Theorem 5.12** (arXiv 2212.02371, `th:icones-tens-limpl-isom`). For each integrable cones $B,C,D$, the function $\Phi_{B,C,D}$ is an isomorphism of integrable cones from $(B\otimes C)\multimap D$ to $B\multimap(C\multimap D)=(B,C\multimap D)$.

```coq
(* theories/homs/tensor.v — Section Tensor *)
Definition tensor_hom_Phi (B C D : ICone.type Ar) :
    icones_iso Ar ((B ⊗ C) ⊸ D) (B ⊸ (C ⊸ D)) :=
  tensor_hom_iso B C D.
```

### Thm 5.13 (`tensor_norm_le`, `tensor_normME`)

The norm of a pure tensor $x\otimes y$ is exactly the product of the two norms $\lVert x\rVert\,\lVert y\rVert$.

> **Paper — Theorem 5.13** (arXiv 2212.02371). For each $x\in\underline{B}$ and $y\in\underline{C}$ we have $\lVert x\otimes y\rVert=\lVert x\rVert\,\lVert y\rVert$.

> **Difference.** The paper states the equality directly; the formalization splits it into `tensor_norm_le` (the $\le$ direction, from $\tau_{B,C}\in\mathbf{ICones}(B,C\multimap(B\otimes C))$) and `tensor_normME` (the full equality). *Why:* the $\ge$ direction relies on the dual-norm characterisation of Prop 3.11, so it is factored out as a separate step.

```coq
(* theories/homs/tensor.v *)
Lemma tensor_norm_le (B C : ICone.type Ar) (x : B) (y : C) :
  cone_norm (x ⊗p y) <= cone_norm x * cone_norm y.

Lemma tensor_normME (B C : ICone.type Ar) (x : B) (y : C) :
  cone_norm (x ⊗p y) = cone_norm x * cone_norm y.
```

### Prop 5.14 (`tensor_ext`, `tensor_ext3`, `tensor_ext4`)

A morphism out of an iterated tensor $t^{\otimes}(\vec B)$ — shaped by a binary tree $t$ with $n$ leaves — is determined by its values on pure iterated tensors $t^{\otimes}(\vec x)$. This extensionality principle is the tool used to check the SMCC coherence diagrams; the formalization spells out the cases $n=2,3,4$ (`tensor_ext`, `tensor_ext3`, `tensor_ext4`) needed for the triangle, pentagon and hexagon.

> **Paper — Proposition 5.14** (arXiv 2212.02371, `prop:fun-ttree-charact`). Let $n\in\mathbb{N}^{+}$, $B_1,\dots,B_n,C$ be integrable cones and $t\in\mathcal{T}_{n}$. Let $f,g\in\mathbf{ICones}(t^{\otimes}(\overrightarrow{B}),C)$. If, for all $(x_i\in\underline{B_i})_{i=1}^n$ one has $f(t^{\otimes}(\overrightarrow{x}))=g(t^{\otimes}(\overrightarrow{x}))$, then $f=g$.

```coq
(* theories/homs/tensor.v *)
Lemma tensor_ext (B C D : ICone.type Ar)
    (f g : icones_hom Ar (B ⊗ C) D) :
  (forall (x : B) (y : C), f (x ⊗p y) = g (x ⊗p y)) -> f = g.

Lemma tensor_ext3 (A B C D : ICone.type Ar)
    (f g : icones_hom Ar ((A ⊗ B) ⊗ C) D) :
  (forall (x : A) (y : B) (z : C),
     f ((x ⊗p y) ⊗p z) = g ((x ⊗p y) ⊗p z)) -> f = g.

(* theories/homs/smcc.v *)
Lemma tensor_ext4 (A B C D E : ICone.type Ar)
    (f g : icones_hom Ar (((A ⊗ B) ⊗ C) ⊗ D) E) :
  (forall (w : A) (x : B) (y : C) (z : D),
     f (((w ⊗p x) ⊗p y) ⊗p z) = g (((w ⊗p x) ⊗p y) ⊗p z)) -> f = g.
```

### Thm 5.15 (`ICones_SMCC`, `ICones_smcc`)

The category $\mathbf{ICones}$, with tensor product $\otimes$ and unit $1$, is a symmetric monoidal closed category: the internal hom is $\multimap$ and the closure iso is Thm 5.12. The `ICones_SMCC` record bundles the bifunctor, unit, structural isos (associator, unitors, braiding) with the triangle, pentagon and hexagon coherences; `ICones_smcc` is the canonical instance.

> **Paper — Theorem 5.15** (arXiv 2212.02371, `th:icones-smcc`). The category $\mathbf{ICones}$, equipped with the bifunctor $\otimes$ and unit $1$ has a structure of symmetric monoidal category, and this SMC is closed.

```coq
(* theories/homs/smcc.v *)
Record ICones_SMCC (R : realType) (Ar : MeasSubcat R) : Type :=
  MkIConesSMCC {
  (* monoidal product and unit *)
  smcc_tensor : ICone.type Ar -> ICone.type Ar -> ICone.type Ar;
  smcc_unit   : ICone.type Ar;
  smcc_mor    : forall B1 B2 C1 C2 : ICone.type Ar,
    icones_hom Ar B1 B2 -> icones_hom Ar C1 C2 ->
    icones_hom Ar (smcc_tensor B1 C1) (smcc_tensor B2 C2);
  smcc_mor_id : (* functoriality on identities *) _;
  (* structural isos *)
  smcc_assoc  : forall A B C, icones_iso Ar _ _;
  smcc_lunit  : forall A, icones_iso Ar (smcc_tensor smcc_unit A) A;
  smcc_runit  : forall A, icones_iso Ar (smcc_tensor A smcc_unit) A;
  smcc_braid  : forall A B, icones_iso Ar (smcc_tensor A B) (smcc_tensor B A);
  (* symmetry, triangle, pentagon, hexagon coherences *)
  smcc_braid_invol : _; smcc_triangle : _;
  smcc_pentagon    : _; smcc_hexagon  : _;
  (* internal hom and the Thm 5.12 closure iso *)
  smcc_hom    : ICone.type Ar -> ICone.type Ar -> ICone.type Ar;
  smcc_closed : forall B C D,
    icones_iso Ar (smcc_hom (smcc_tensor B C) D)
                  (smcc_hom B (smcc_hom C D));
}.

Definition ICones_smcc (R : realType) (Ar : MeasSubcat R) :
    ICones_SMCC Ar :=
  {| smcc_tensor := @tensor R Ar;
     smcc_unit   := cone_one_car Ar;
     smcc_mor    := @tensor_mor R Ar;
     smcc_assoc  := @tensor_assoc R Ar;
     smcc_lunit  := @tensor_lunit R Ar;
     smcc_runit  := @tensor_runit R Ar;
     smcc_braid  := @tensor_braid R Ar;
     (* ... coherence witnesses ... *)
     smcc_hom    := @linhom_car R Ar;
     smcc_closed := @tensor_hom_iso R Ar |}.
```

---

## Paper § 6 — Substochastic kernels and the embedding theorem

| Paper | English statement | Rocq |
|---|---|---|
| Cat 6 | The category $\mathbf{Skern}$ of substochastic kernels: objects in $\mathbf{Ar}$, morphisms $\kappa : X \leadsto \mathsf{FMeas}(Y)$. | `Skern_hom`, `Skern_id`, `Skern_comp`, `Skern` — `theories/kernels/skern.v` |
| Thm 6.1 | Bijection $\mathsf{Path}(X, B) \simeq \mathsf{FMeas}(X) \multimap B$ (cone iso) given by the integration map $\mathcal{I}^{B}_X$. | `int_to_linhom`, `int_to_linhom_iso` — `theories/homs/bilin.v` |
| Thm 6.5 | The functor $\mathsf{Klin} : \mathbf{Skern} \to \mathbf{ICones}$, sending $X \mapsto \mathsf{FMeas}(X)$ and a kernel to its integration map, is **fully faithful**. | `Skern_to_ICones_fully_faithful` (= the *regression anchor*) — `theories/kernels/kernel_embedding.v` |

`Skern_to_ICones_fully_faithful` is the lemma checked by `./verify.sh` and is
load-bearing for the whole development's axiom budget. It depends only on the
3 classical `boolp` axioms.

### Cat 6 (`Skern_hom`, `Skern_id`, `Skern_comp`)

The category $\mathbf{Skern}$ of substochastic kernels has the objects of $\mathbf{Ar}$; a kernel $X\to Y$ is an element of $\mathbf{Skern}(X,Y)=\mathcal{B}(\underline{\mathsf{Path}(X,\mathsf{FMeas}(Y))})$, i.e. a measurable path of unit-ball norm. The identity at $X$ is the Dirac path $\boldsymbol\delta^{X}$, and composition is Kleisli composition $\kappa=\kappa_2\,\kappa_1$ with $\kappa(r_1)=\mathcal{I}^{\mathsf{FMeas}(X_3)}_{X_2}(\kappa_2)(\kappa_1(r_1))$, the continuous generalisation of the product of substochastic matrices.

> **Paper — §6.1 "The category of substochastic kernels as a full subcategory of $\mathbf{ICones}$"** (arXiv 2212.02371, `content.tex:4574`). If $X,Y\in\mathbf{Ar}$, a substochastic kernel from $X$ to $Y$ is an element of $\mathbf{Skern}(X,Y)=\mathcal{B}(\underline{\mathsf{Path}(X,\mathsf{FMeas}(Y))})$. Then $\mathbf{Skern}$ is the category whose objects are those of $\mathbf{Ar}$ and: the identity at $X$ is $\boldsymbol\delta^{X}\in\mathbf{Skern}(X,X)$; and given $\kappa_1\in\mathbf{Skern}(X_1,X_2)$ and $\kappa_2\in\mathbf{Skern}(X_2,X_3)$, their composite $\kappa=\kappa_2\,\kappa_1$ is given by $\kappa(r_1)(U_3)=\int^{1}_{r_2\in X_2}\kappa_2(r_2,U_3)\kappa_1(r_1,dr_2)$ for $U_3\in\sigma_{X_3}$, that is $\kappa(r_1)=\mathcal{I}^{\mathsf{FMeas}(X_3)}_{X_2}(\kappa_2)(\kappa_1(r_1))$.

```coq
(* theories/kernels/skern.v — Section SkernHom, Variables R Ar *)
Record Skern_hom (X Y : ar_obj Ar) : Type := MkSkernHom {
  skern_path     : path_car Ar X (fmeas R (ar_carrier Ar Y));
  skern_norm_le1 : path_norm skern_path <= 1;
}.

Definition Skern_id : Skern_hom Ar X X :=
  MkSkernHom (dirac_path Ar X) dirac_path_norm_le1.

Definition Skern_comp_path (λ : Skern_hom Ar X Y) (κ : Skern_hom Ar Y Z) :
    path_car Ar X (fmeas R (ar_carrier Ar Z)) :=
  MkPath (int_to_linhom_fun_pres_path (skern_path κ)
            (path_is_path (skern_path λ))).

Definition Skern_comp (λ : Skern_hom Ar X Y) (κ : Skern_hom Ar Y Z) :
    Skern_hom Ar X Z :=
  MkSkernHom (Skern_comp_path λ κ) (Skern_comp_norm_le1 λ κ).
```

### Thm 6.1 (`int_to_linhom`, `int_to_linhom_iso`)

For each $X\in\mathbf{Ar}$ and integrable cone $B$, the integration operator $\mathcal{I}^{B}_X$ realises a natural isomorphism between the path cone $\mathsf{Path}(X,B)$ and the linear-hom cone $\mathsf{FMeas}(X)\multimap B$, with inverse $f\mapsto f\circ\boldsymbol\delta^{X}$. The formalization packages the underlying map $\mu\mapsto\int\beta(r)\mu(dr)$ as a `linhom_car` and exhibits the bijection as a `cones_iso`.

> **Paper — Theorem 6.1** (arXiv 2212.02371, `th:meas-path-equiv`). For each $X\in\mathbf{Ar}$ and integrable cone $B$, one has $\mathcal{I}^{B}_X\in\mathbf{ICones}(\mathsf{Path}(X,B),\mathsf{FMeas}(X)\multimap B)$ and $\mathcal{I}^{B}_X$ (this notation is introduced in Definition~\ref{def:integral-in-cone}) is an isomorphism which is natural in $X$ and in $B$ (between functors $\mathbf{Ar}^{\mathsf{op}}\times\mathbf{ICones}\to\mathbf{ICones}$).

> **Difference.** The paper states the isomorphism in $\mathbf{ICones}$ (both $\mathcal{I}^{B}_X$ and its inverse preserve integrals), whereas `int_to_linhom_iso` mechanises it as a `cones_iso` — an iso of the underlying cones. *Why:* the load-bearing content for the embedding theorem is the underlying bijection $\mathsf{Path}(X,B)\simeq\mathsf{FMeas}(X)\multimap B$; the extra $\mathbf{ICones}$-naturality is not needed downstream and is not carried by this definition.

```coq
(* theories/homs/bilin.v *)
Definition int_to_linhom_fun :
    fmeas R (ar_carrier Ar X) -> B :=
  fun µ => icone_integral βf Hβ µ.

Definition int_to_linhom :
    linhom_car Ar (fmeas R (ar_carrier Ar X)) B :=
  MkLinhom int_to_linhom_pre
    (fun Y β' Hβ' µ' => int_to_linhom_fun_pres_int β Hβ' µ').

Definition int_to_linhom_iso : cones_iso P L :=
  MkConesIso int_to_linhom_cones linhom_to_int_cones
    int_to_linhom_conesK int_to_linhom_conesK'.
```

### Thm 6.5 (`Skern_to_ICones_fully_faithful`)

The functor $\mathsf{Klin}:\mathbf{Skern}\to\mathbf{ICones}$, sending $X\mapsto\mathsf{FMeas}(X)$ and a kernel $\kappa$ to $\mathcal{I}^{\mathsf{FMeas}(Y)}_X(\kappa)$, embeds substochastic kernels as a full subcategory of $\mathbf{ICones}$. The regression anchor `Skern_to_ICones_fully_faithful` mechanises full-and-faithfulness as the conjunction of injectivity (faithful) and surjectivity-on-hom-sets (full) of the map $\kappa\mapsto\mathsf{Klin}(\kappa)$ on morphisms $\mathsf{FMeas}(X)\to\mathsf{FMeas}(Y)$.

> **Paper — Theorem 6.5** (arXiv 2212.02371). The functor $\mathsf{Klin}:\mathbf{Skern}\to\mathbf{ICones}$ is full and faithful.

```coq
(* theories/kernels/kernel_embedding.v *)
Theorem Skern_to_ICones_fully_faithful (X Y : ar_obj Ar) :
  (forall κ1 κ2 : Skern_hom Ar X Y,
     Skern_to_ICones_mor κ1 = Skern_to_ICones_mor κ2 -> κ1 = κ2) /\
  (forall f : icones_hom Ar (fmeas R (ar_carrier Ar X))
                            (fmeas R (ar_carrier Ar Y)),
     exists κ : Skern_hom Ar X Y, Skern_to_ICones_mor κ = f).
Proof.
by split; [exact: Skern_to_ICones_faithful | exact: Skern_to_ICones_full].
Qed.
```

---

## Paper § 7 — Stable functions and the cartesian-closed category SCones

| Paper | English statement | Rocq |
|---|---|---|
| Def 7.5 | A function $f:\mathcal{B}P\to Q$ is *totally monotonic* if its iterated finite differences over the parity lattice satisfy $\sum_{I\in\mathcal{P}^-(n)}f(x+\sum_{i\in I}u_i)\le\sum_{I\in\mathcal{P}^+(n)}f(x+\sum_{i\in I}u_i)$. | `is_totmono`, `Pneg`/`Ppos` — `theories/stable/totmono.v` |
| Def 7.7 | A function is *stable* if it is totally monotonic, bounded, and $\omega$-continuous on the unit ball. | `is_stable` (uses `is_scott_continuous_unit`) — `theories/stable/totmono.v` |
| Def 7.10 | A *measurable stable* function additionally sends measurable paths $X\to C$ to measurable paths $X\to D$. | `is_meas_stable` — `theories/stable/totmono.v` |
| Lem 7.11 | The stable and measurable functions $C\to D$ form a precone under pointwise operations (closed under $0$, addition, and non-negative scaling). | `stable_zero`, `stable_add`, `stable_scale` — `theories/stable/totmono.v` |
| Lem 7.12 | The stable (cone) order coincides with the alternating finite-difference inequality: $f\le g$ iff a sign-split difference test holds. | `sh_le_of_alt` — `theories/stable/stablehom.v` |
| Thm 7.19 | $f$ is totally monotonic iff it is *$n$-increasing* for every $n\in\mathbb{N}$. | `totmono_is_n_increasing` (forward), `is_n_increasing_totmono` (converse) — `theories/stable/findiff.v` |
| Lem 7.20–7.25 | The finite-difference / sign-split machinery $\Delta^{\epsilon}$, $\Delta$, $\mathsf{S}^n B$ used to prove Thm 7.19 and the §7.3 closure properties. | `totmono_Delta_pos`/`_neg`, `SD`, `SD_cons`, `SnB`, `SnB_increasing`, etc. — `theories/stable/findiff.v` + `theories/stable/compose.v` |
| Lem 7.27 | If $f$ is linear in its first argument and totally monotonic in its second, it is totally monotonic on the product of unit balls. | `ev_totmono` (delivered in the form actually needed by the CCC) — `theories/stable/scones_ccc.v` |
| Thm 7.30 | Stable (and measurable) functions of norm $\le 1$ are closed under composition. | `stable_comp`, `meas_stable_comp` — `theories/stable/compose.v` |
| Thm 7.32 | The category $\mathbf{SCones}$ of stable functions has all products and is cartesian closed. | `SCones_ccc`, `SCones_CCC` (record + witness) — `theories/stable/scones_ccc.v` |
| Thm 7.34 | The forgetful functor $\mathsf{Der}:\mathbf{ICones}\to\mathbf{SCones}$ preserves all limits. | `der_preserves_prod_proj`, `der_preserves_limits` — `theories/stable/der_continuous.v` |
| (also) | Stable functions admit a least fixpoint via the cone unit-ball $\omega$-cpo (paper §9.2). | `lfp_fixpoint`, `sfix_fixpoint`, `Yfix`, `Yfix_fix` — `theories/stable/fixpoint.v` |

The `is_stable` predicate uses `is_scott_continuous_unit` (unit-ball input,
any-radius output sup) because the strictly-linear `is_omega_continuous`
(both $\omega$-chains in the unit ball) is **not preserved under non-negative
scaling for non-linear maps** — a faithful reading of the paper's setting,
not a weakening.

### Def 7.5 (`is_totmono`, `Pneg`, `Ppos`)

Total monotonicity is an inclusion-exclusion inequality over the odd- and even-parity subsets $\mathcal{P}^-(n)$, $\mathcal{P}^+(n)$ of $\{1,\dots,n\}$, generalizing absolute monotonicity to cones. `Pneg`/`Ppos` partition the powerset of $\{1,\dots,n\}$ by the parity of $n-\lvert I\rvert$.

> **Paper — Definition 7.5** (arXiv 2212.02371, `def:totally-monotonic`). Let $P$ and $Q$ be cones, a function $f:\mathcal{B}P\to Q$ is *totally monotonic* if for each $n\in\mathbb{N}$ and each $x,u_1,\dots,u_n\in P$ such that $x+\sum_{i=1}^n u_i\in\mathcal{B}P$ one has $$\sum_{I\in\mathcal{P}^-(n)}f\Big(x+\sum_{i\in I}u_i\Big)\leq\sum_{I\in\mathcal{P}^+(n)}f\Big(x+\sum_{i\in I}u_i\Big)\,.$$

```coq
(* theories/stable/totmono.v — Section variables: R : realType, P Q : coneType R *)
Definition Pneg (n : nat) : {set {set 'I_n}} :=
  [set I in powerset [set: 'I_n] | odd (n - #|I|)].
Definition Ppos (n : nat) : {set {set 'I_n}} :=
  [set I in powerset [set: 'I_n] | ~~ odd (n - #|I|)].

Definition tm_arg (n : nat) (x : P) (u : 'I_n -> P) (I : {set 'I_n}) : P :=
  x + \big[precone_add/precone_zero]_(i in I) u i.

Definition is_totmono (f : P -> Q) : Prop :=
  forall (n : nat) (x : P) (u : 'I_n -> P),
    cone_norm (x + \big[precone_add/precone_zero]_(i : 'I_n) u i) <= 1 ->
    precone_le
      (\big[precone_add/precone_zero]_(I in Pneg n) f (tm_arg x u I))
      (\big[precone_add/precone_zero]_(I in Ppos n) f (tm_arg x u I)).
```

### Def 7.7 (`is_stable`)

A *stable* function is a totally monotonic, bounded, $\omega$-continuous map on the unit ball.

> **Paper — Definition 7.7** (arXiv 2212.02371). Let $P$ and $Q$ be cones. A function $f:\mathcal{B}P\to Q$ is *stable* if $f$ is totally monotonic, bounded and $\omega$-continuous (see Definition 2.2).

> **Difference.** `is_stable` uses `is_scott_continuous_unit` (unit-ball input, any-radius output sup) rather than the strictly-linear `is_omega_continuous`. *Why:* the latter (both $\omega$-chains constrained to the unit ball) is not preserved under non-negative scaling for non-linear maps; the unit-ball form is a faithful reading of the paper's setting, not a weakening.

```coq
(* theories/stable/totmono.v *)
Definition is_stable (f : P -> Q) : Prop :=
  [/\ is_totmono f,
      exists M : R, forall x : P, cone_norm x <= 1 -> cone_norm (f x) <= M
   &  is_scott_continuous_unit f].
```

### Def 7.10 (`is_meas_stable`)

A stable function $f:\mathcal{B}\underline{C}\to\underline{D}$ is *measurable* when post-composition sends every measurable path into $C$ to a measurable path into $D$.

> **Paper — Definition 7.10** (arXiv 2212.02371). Let $C,D$ be measurable cones. A stable function $f:\mathcal{B}\underline{C}\to\underline{D}$ is measurable if for each $X\in\mathbf{Ar}$ and $\gamma\in\mathcal{B}\underline{\mathsf{Path}(X,C)}$ one has $f\mathrel{\circ}\gamma\in\underline{\mathsf{Path}(X,D)}$.

```coq
(* theories/stable/totmono.v — Variables R Ar (C D : MCone.type Ar) *)
Definition is_meas_stable (f : C -> D) : Prop :=
  is_stable f /\
  forall (X : ar_obj Ar) (γ : ar_carrier Ar X -> C),
    (forall r, cone_norm (γ r) <= 1) ->
    is_measurable_path (Ar:=Ar) (C:=C) γ ->
    is_measurable_path (Ar:=Ar) (C:=D) (fun r => f (γ r)).
```

### Lem 7.11 (`stable_zero`, `stable_add`, `stable_scale`)

The stable (and measurable) functions $C\to D$, equipped with pointwise algebraic operations, form a precone; the three lemmas record closure under $0$, addition, and non-negative scaling.

> **Paper — Lemma 7.11** (arXiv 2212.02371). The set of stable and measurable functions $C\to D$, equipped with algebraic operations defined pointwise, is a precone.

```coq
(* theories/stable/totmono.v *)
Lemma stable_zero : is_stable stm_zero.

Lemma stable_add (f g : P -> Q) :
  is_stable f -> is_stable g -> is_stable (stm_add f g).

Lemma stable_scale (r : {nonneg R}) (f : P -> Q) :
  is_stable f -> is_stable (stm_scale r f).
```

### Lem 7.12 (`sh_le_of_alt`)

The cone (stable) order on the precone of stable functions is characterized by a finite-difference inequality between $f$ and $g$; `sh_le_of_alt` is the backward direction — the alternating-sum inequality implies the pointwise stable (precone) order.

> **Paper — Lemma 7.12** (arXiv 2212.02371, `lemma:stable-order-charact`). Let $f,g\in P$. One has $f\leq g$ iff for each $n\in\mathbb{N}$ and each $x,u_1,\dots,u_n\in\mathcal{B}\underline{C}$ such that $x+\sum_{i=1}^n u_i\in\mathcal{B}\underline{C}$ one has $$\sum_{I\in\mathcal{P}^-(n)}g\Big(x+\sum_{i\in I}u_i\Big)+\sum_{I\in\mathcal{P}^+(n)}f\Big(x+\sum_{i\in I}u_i\Big)\leq\sum_{I\in\mathcal{P}^+(n)}g\Big(x+\sum_{i\in I}u_i\Big)+\sum_{I\in\mathcal{P}^-(n)}f\Big(x+\sum_{i\in I}u_i\Big)\,.$$

```coq
(* theories/stable/stablehom.v *)
Lemma sh_le_of_alt : precone_le f g.
Proof. by exists sh_diff; rewrite -sh_add_diff. Qed.
```

### Thm 7.19 (`totmono_is_n_increasing`, `is_n_increasing_totmono`)

Total monotonicity is equivalent to being $n$-increasing for every $n$ (the inductive characterization via iterated first differences over local cones). The two lemmas give the forward and converse directions.

> **Paper — Theorem 7.19** (arXiv 2212.02371, `th:induct-total-nonotone`). A function $f\in\mathcal{B}\underline{B}\to\underline{C}$ is totally monotonic iff it is $n$-increasing for all $n\in\mathbb{N}$.

> **Difference.** The converse `is_n_increasing_totmono` carries an extra `is_scott_continuous_unit` hypothesis, and is proved on the closed unit ball. *Why:* the finite-difference recovery of the parity inequality is established $\omega$-continuously on the ball.

```coq
(* theories/stable/findiff.v *)
Lemma totmono_is_n_increasing (n : nat) (R : realType) (B C : coneType R)
    (f : B -> C) : is_totmono f -> is_n_increasing n f.

(* Variables: R B C f. *)
Lemma is_n_increasing_totmono :
  (forall k, is_n_increasing k f) -> is_scott_continuous_unit f ->
  is_totmono f.
```

### Lem 7.20–7.25 (finite-difference $\Delta^{\epsilon}$ / $\Delta$ / SD / SnB machinery)

The signed finite-difference machinery driving Thm 7.19 and the §7.3 closure properties. `totmono_Delta` packages Lemma 7.20 — for totally monotonic $f$, the positive, negative, and full iterated differences $\Delta^+f(\overrightarrow{u})$, $\Delta^-f(\overrightarrow{u})$, $\Delta f(\overrightarrow{u})$ are totally monotonic on the residual ball — while `SnB_increasing` packages Lemma 7.25, that the global iterated-difference map $(x,\overrightarrow{u})\mapsto\Delta f(\overrightarrow{u})(x)$ is increasing on the auxiliary cone $\mathsf{S}^n B$.

> **Paper — Lemma 7.20** (arXiv 2212.02371, `lemma:fdiff-tot-mon`). Let $f:\mathcal{B}\underline{B}\to\underline{C}$ be totally monotonic and $\overrightarrow{u}\in\underline{B}^n$ be such that $\sum_{i=1}^n u_i\in\mathcal{B}\underline{B}$. Then the functions $\Delta^+ f(\overrightarrow{u}),\Delta^- f(\overrightarrow{u}),\Delta f(\overrightarrow{u}):\mathcal{B}\underline{B_{\overrightarrow{u}}}\to\underline{C}$ are totally monotonic.

> **Paper — Lemma 7.25** (arXiv 2212.02371, `lemma:fdiff-glob-increasing`). If $f:\mathcal{B}\underline{B}\to\underline{C}$ is totally monotonic, the map $(x,\overrightarrow{u})\to\Delta f(\overrightarrow{u})(x)$ is increasing $\mathcal{B}\mathsf{S}^n B\to\underline{C}$.

```coq
(* theories/stable/findiff.v + theories/stable/compose.v *)

(* [totmono_Delta]: the finite-difference [Δf(u⃗) := SDpos f − SDneg f]
   on the unit ball, packaging Δε / Δ for ε ∈ {+, −}. *)
Lemma totmono_Delta (n : nat) (u : 'I_n -> B)
    (Hs : (* sum bound on u *)) :
  (* totmono of f gives totmono of Δf(u⃗) on the residual ball *).

(* [SnB]: the "[(x, u⃗) ∈ B_n]" predicate; Lemma 7.25 says
   [(x,u⃗) ↦ Δf(u⃗)(x)] is increasing on it. *)
Definition SnB_diff (g : SnB B n) : C := (* Δf(u⃗)(x) for g = (x, u⃗) *).
Lemma SnB_increasing : is_increasing SnB_diff.
```

### Lem 7.27 (`ev_totmono`)

A function linear in one argument and totally monotonic in the other is totally monotonic on the product of the unit balls; `ev_totmono` delivers this in the form the CCC needs — evaluation is totally monotonic on the $\mathbf{SCones}$ product $\mathbf{SCones}(B,C)\times B$.

> **Paper — Lemma 7.27** (arXiv 2212.02371, `lemma:lin-tot-mon-is-tot-mon`). Let $f:\underline{B}\times\mathcal{B}\underline{C}\to\underline{D}$ be linear in its first argument and totally monotonic in its second argument. Then, when restricted to $\mathcal{B}\underline{B}\times\mathcal{B}\underline{C}$, the function $f$ is totally monotonic.

> **Difference.** The paper states 7.27 for a general two-argument $f$; the formalization instantiates it directly at the evaluation map `ev_fun` on the $\mathbf{SCones}$ product — the only instance the cartesian-closed structure requires.

```coq
(* theories/stable/scones_ccc.v *)
Lemma ev_totmono : is_totmono ev_fun.
```

### Thm 7.30 (`stable_comp`, `meas_stable_comp`)

Stable and measurable functions of norm $\le 1$ are closed under composition (the well-definedness of the category $\mathbf{SCones}$). `stable_comp` handles the stable part and `meas_stable_comp` the measurable-path-preservation part.

> **Paper — Theorem 7.30** (arXiv 2212.02371). If $f\in\mathbf{SCones}(B,C)$ and $g\in\mathbf{SCones}(C,D)$ then $g\mathrel{\circ}f\in\mathbf{SCones}(B,D)$.

```coq
(* theories/stable/compose.v *)
Lemma stable_comp (f : B -> C) (g : C -> D)
    (Hf : is_stable f) (Hg : is_stable g)
    (Hfb : forall x, cone_norm x <= 1 -> cone_norm (f x) <= 1) :
  is_stable (fun x => g (f x)).

Lemma meas_stable_comp (R : realType) (Ar : MeasSubcat R)
    (B C D : MCone.type Ar) (f : B -> C) (g : C -> D)
    (Hf : is_meas_stable f) (Hg : is_meas_stable g)
    (Hfb : forall x, cone_norm x <= 1 -> cone_norm (f x) <= 1) :
  is_meas_stable (fun x => g (f x)).
```

### Thm 7.32 (`SCones_CCC`, `SCones_ccc`)

The category $\mathbf{SCones}$ of integrable cones and stable/measurable functions has all products and is cartesian closed, with internal hom the cone $\mathbf{SCones}(B,C)$ and evaluation morphism $\mathsf{Ev}(f,x)=f(x)$. `SCones_CCC` is the record packaging the product and exponential data with their $\beta$/$\eta$ laws; `SCones_ccc` is the witness assembled from `sprod`, `Ev`, `curry`, etc.

> **Paper — Theorem 7.32** (arXiv 2212.02371). The category $\mathbf{SCones}$ has all products and is cartesian closed.

```coq
(* theories/stable/scones_ccc.v *)
Record SCones_CCC (R : realType) (Ar : MeasSubcat R) : Type := {
  (* binary product *)
  ccc_prod : ICone.type Ar -> ICone.type Ar -> ICone.type Ar;
  ccc_fst  : forall X Y, scones_hom (ccc_prod X Y) X;
  ccc_snd  : forall X Y, scones_hom (ccc_prod X Y) Y;
  ccc_pair : forall Q X Y,
    scones_hom Q X -> scones_hom Q Y -> scones_hom Q (ccc_prod X Y);
  ccc_pair_fst : (* β law on fst *) _;
  ccc_pair_snd : (* β law on snd *) _;
  (* exponential *)
  ccc_exp   : ICone.type Ar -> ICone.type Ar -> ICone.type Ar;
  ccc_ev    : forall B C, scones_hom (ccc_prod (ccc_exp B C) B) C;
  ccc_curry : forall D B C,
    scones_hom (ccc_prod D B) C -> scones_hom D (ccc_exp B C);
  ccc_beta  : (* β law of the exponential *) _;
  ccc_eta   : (* η law of the exponential *) _;
}.

Definition SCones_ccc : SCones_CCC Ar :=
  {| ccc_prod  := @sprod R Ar;
     ccc_fst   := @sfst;
     ccc_snd   := @ssnd;
     ccc_pair  := @spair;
     ccc_pair_fst := @spair_fst;
     ccc_pair_snd := @spair_snd;
     ccc_exp   := fun B C => (stablehom B C : ICone.type Ar);
     ccc_ev    := @Ev R Ar;
     ccc_curry := @curry R Ar;
     ccc_beta  := @scones_beta;
     ccc_eta   := @scones_eta |}.
```

### Thm 7.34 (`der_preserves_prod_proj`, `der_preserves_limits`)

The forgetful (dereliction) functor $\mathsf{Der}:\mathbf{ICones}\to\mathbf{SCones}$ preserves all limits — both products and equalizers. `der_preserves_prod_proj` records the (definitional) product case and `der_preserves_limits` bundles the equalizer case.

> **Paper — Theorem 7.34** (arXiv 2212.02371, `th:derfuns-preserves-limits`). The functor $\mathsf{Der}:\mathbf{ICones}\to\mathbf{SCones}$ preserves all limits.

```coq
(* theories/stable/der_continuous.v *)

(* [Der] sends the [i]-th ICones projection to the [i]-th SCones projection. *)
Lemma der_preserves_prod_proj (i : I) :
  ders (icones_proj i) = scones_proj D i.
Proof. by []. Qed.

Record der_continuous : Prop := MkDerContinuous {
  dc_eq_equ : (* equaliser identity *) _;
  dc_eq_med : (* mediator with factor + uniqueness *) _;
}.

Theorem der_preserves_limits : der_continuous.
```

### §9.2 (`lfp_fixpoint`, `sfix_fixpoint`, `Yfix`, `Yfix_fix`)

Stable functions admit a least fixpoint via the cone unit-ball $\omega$-cpo: the Kleene chain $u_n=f^n(0)$ has a supremum $\mathsf{lfp}(f)=\sup_n u_n$ which is a fixpoint, packaged as the least-fixpoint combinator $\mathsf{Y}$ realized as an $\mathbf{SCones}$ morphism. This supports the fixpoint semantics of paper §9.2; it corresponds to no single numbered statement in §7, so no paper statement is quoted here.

```coq
(* theories/stable/fixpoint.v *)

(* [lfp f = sup uₙ] for the Kleene chain [uₙ = fⁿ 0] is a fixpoint. *)
Lemma lfp_fixpoint : f (lfp f f_incr f_ball) = lfp f f_incr f_ball.

(* [sfix f := lfp (sc_fun f) ...] is a fixpoint of the stable f. *)
Lemma sfix_fixpoint (f : scones_hom B B) : sc_fun f (sfix f) = sfix f.

(* The least-fixpoint combinator [Y] as an SCones morphism. *)
Definition Yfix : scones_hom BB B :=
  MkSconesHom (sh_fun Yfix_elt) (sh_meas_stable Yfix_elt) Yfix_norm_le1
    (sh_offball Yfix_elt).

(* The fixpoint equation [Yfix f = f (Yfix f)] on the unit ball. *)
Lemma Yfix_fix (f : BB) :
  cone_norm f <= 1 -> sh_fun f (sc_fun Yfix f) = sc_fun Yfix f.
```

---

## Paper § 9 — Linear exponential, Seely category, FMeas coalgebra

| Paper | English statement | Rocq |
|---|---|---|
| LL $!$ | The linear-exponential comonad $! : \mathbf{ICones} \to \mathbf{ICones}$, obtained as $! = \mathsf{E}\circ\mathsf{Der}$ where $\mathsf{E}$ is the left adjoint of $\mathsf{Der}$ (existing by the special adjoint functor theorem). | `Bang`, `nl`, `lin`, `lin_beta`, `lin_unique` (the adjunction data) — `theories/homs/exp_adjunction.v`; `Bang_comonad` — `theories/homs/bang.v` |
| Comonad | $(!, \mathsf{der}, \mathsf{dig})$ is a comonad with the standard counit / coassociativity, satisfying $\mathsf{der}_B(x^!)=x$ and $\mathsf{dig}_B(x^!)=x^{!!}$. | `der`, `dig`, `der_prom`, `dig_prom`, the comonad laws — `theories/homs/bang.v` |
| Lem 9.4 | The natural iso $(B \Rightarrow (C \multimap D)) \simeq (C \multimap (B \Rightarrow D))$ ("swap a stable outer and a linear inner"). | `stab_lin_swap` (a fully spelled-out `icones_iso`; paper gives the map + "pattern seen many times", no proof) — `theories/stable/stab_lin_swap.v` |
| Thm 9.5 | $(\mathbf{ICones}, \otimes, 1, !)$ is a **Seely category** (i.e. has the Seely isos $\mathsf{m}^2 : {!B_1} \otimes {!B_2} \simeq {!(B_1 \mathrel{\&} B_2)}$ and $\mathsf{m}^0 : 1 \simeq {!\top}$, and the comonad / SMC coherence). | `Seely2`, `Seely2E`, `Seely2_natural`, `Seely0`, `Seely0E`, the full `SeelyCategory` record + the witness `ICones_Seely` — `theories/homs/seely.v` |
| Thm 9.7 | For each $X \in \mathbf{Ar}$, $\mathsf{FMeas}(X)$ is a $!$-coalgebra (with structure map $\mathsf{h}_X(\mu) = \int_{r\in X} (\boldsymbol\delta^X(r))^! \,\mu(dr)$); the assignment $X \mapsto \mathsf{FMeas}(X)$ is a functor into $\mathbf{ICones}^!$. | `Coalg`, `Coalg_dirac`, `dirac_dense`, `FMeas_coalgebra`, `FMeas_fmap` — `theories/homs/coalgebra.v` |
| Sect 9.2 | Fixpoint combinator $\mathcal{Y}$ on the cartesian closed $\mathbf{SCones}$. | `Yfix`, `Yfix_fix` (the paper's CCC construction) — `theories/stable/fixpoint.v` |

### Linear exponential `!` (`Bang`, `nl`, `lin`, `lin_beta`, `lin_unique`)

The linear exponential ${!B} = \mathsf{E}(B)$ is the object part of the left adjoint $\mathsf{E}$ of $\mathsf{Der} : \mathbf{ICones}\to\mathbf{SCones}$. Its universal property is the *universal nonlinear map* $\mathsf{nl}_B \in \mathbf{SCones}(B, {!B})$ (the unit of the adjunction): every stable map $f\in\mathbf{SCones}(B,C)$ factors as $f = \mathsf{der}(\phi)\circ\mathsf{nl}_B$ for a *unique* linear $\phi\in\mathbf{ICones}({!B},C)$, written $\mathsf{lin}\,f = \Theta^{-1}_{B,C}(f)$. Writing $x^! = \mathsf{nl}_B(x)$ for $x$ in the unit ball, this gives $f(x) = (\mathsf{lin}\,f)(x^!)$.

> **Paper — §9** (arXiv 2212.02371, `sec:lin-nonlin-adj`). Let $\mathsf{E} : \mathbf{SCones}\to\mathbf{ICones}$ be the left adjoint of $\mathsf{Der}$, which exists by Theorem 4.19, and $\Theta_{B,C} : \mathbf{ICones}(\mathsf{E}B,C)\to\mathbf{SCones}(B,\mathsf{Der}\,C)=\mathbf{SCones}(B,C)$ the associated natural bijection (remember $\mathsf{Der}\,C=C$). Let $\mathsf{nl}_B=\Theta_{B,\mathsf{E}B}(\mathsf{Id}_{\mathsf{E}B})\in\mathbf{SCones}(B,{!B})$ be the unit of the adjunction, which is the "universal nonlinear map" on $B$ in the sense that for each integrable cone $C$ and each $f\in\mathbf{SCones}(B,C)$ one has $f=\phi\circ\mathsf{nl}_B$ for a unique $\phi\in\mathbf{ICones}({!B},C)$, namely $\phi=\Theta^{-1}_{B,C}(f)$. So that for $h\in\mathbf{ICones}({!B},C)$ one has $\Theta_{B,C}(h)=h\circ\mathsf{nl}_B$. For each $x\in\mathcal{B}\underline{B}$ we set $x^!=\mathsf{nl}_B(x)\in\mathcal{B}\underline{{!B}}$ so that, for $f\in\mathbf{SCones}(B,C)$, we have $f(x)=\Theta^{-1}_{B,C}(f)(x^!)$.

```coq
(* theories/homs/exp_adjunction.v — Section ExpInterface,
   Variables (R : realType) (Ar : MeasSubcat R) *)

Definition Bang (B : ICone.type Ar) : ICone.type Ar :=
  Icones_bang_construct.Bang B.

Definition nl (B : ICone.type Ar) : scones_hom B (Bang B) :=
  Icones_bang_construct.nl B.

Definition lin (B C : ICone.type Ar) (f : scones_hom B C) :
    icones_hom Ar (Bang B) C :=
  Icones_bang_construct.lin f.

Lemma lin_beta (B C : ICone.type Ar) (f : scones_hom B C) :
  scones_comp (ders (lin f)) (nl B) = f.

Lemma lin_unique (B C : ICone.type Ar) (f : scones_hom B C)
    (h : icones_hom Ar (Bang B) C) :
  scones_comp (ders h) (nl B) = f -> h = lin f.
```

### Comonad (`der`, `dig`, `Comonad`, `Bang_comonad`)

The comonad induced on $\mathbf{ICones}$ by the linear-non-linear adjunction has counit $\mathsf{der}_B \in \mathbf{ICones}({!B}, B)$ (dereliction, characterised by $\mathsf{der}_B(x^!) = x$) and comultiplication $\mathsf{dig}_B = \mathsf{E}(\mathsf{nl}_B) \in \mathbf{ICones}({!B}, {!!B})$ (digging, characterised by $\mathsf{dig}_B(x^!) = x^{!!}$). The `Comonad` record bundles the endofunctor $!$ together with `der`, `dig` and the functor / comonad laws; `Bang_comonad` is the canonical, axiom-free witness on $\mathbf{ICones}$.

> **Paper — §9** (arXiv 2212.02371, `sec:lin-nonlin-adj`). We use $(!, \mathsf{der}, \mathsf{dig})$ for the induced comonad on $\mathbf{ICones}$ whose Kleisli category is (equivalent to) $\mathbf{SCones}$. The counit $\mathsf{der}_B\in\mathbf{ICones}({!B},B)$ of the comonad ${!}\_$ is also the counit of the adjunction; it satisfies $\forall x\in\mathcal{B}\underline{B}\ \ \mathsf{der}_B(x^!)=x$. The comultiplication $\mathsf{dig}_B\in\mathbf{ICones}({!B},{!!B})$ is defined by $\mathsf{dig}_B=\mathsf{E}(\mathsf{nl}_B)$ so that $\forall x\in\mathcal{B}\underline{B}\ \ \mathsf{dig}_B(x^!)=x^{!!}$.

> **Difference.** The paper obtains $!$, $\mathsf{der}$, $\mathsf{dig}$ from the abstract left adjoint $\mathsf{E}$; the formalization takes the same route but bundles the comonad as an explicit record `Comonad` (endofunctor + counit + comultiplication + laws) so that the Seely and coalgebra layers can quantify over it. The Kleisli-equivalence discussion is kept informal in the paper and is not part of the mechanised bundle.

```coq
(* theories/homs/bang.v *)

Definition der (B : ICone.type Ar) : icones_hom Ar (Bang Ar B) B :=
  lin (scones_id B).

Lemma der_prom (B : ICone.type Ar) (x : B) :
  cone_norm x <= 1 -> Lfun (der B) x! = x.
Lemma der_nat (B C : ICone.type Ar) (f : icones_hom Ar B C) :
  icones_comp f (der B) = icones_comp (der C) (bang_fmap f).

Definition dig (B : ICone.type Ar) :
    icones_hom Ar (Bang Ar B) (Bang Ar (Bang Ar B)) :=
  lin (scones_comp (nl (Bang Ar B)) (nl B)).

Lemma dig_prom (B : ICone.type Ar) (x : B) :
  cone_norm x <= 1 -> Lfun (dig B) x! = prom (prom x).
Lemma dig_nat (B C : ICone.type Ar) (f : icones_hom Ar B C) :
  icones_comp (bang_fmap (bang_fmap f)) (dig B) =
  icones_comp (dig C) (bang_fmap f).

Record Comonad (R : realType) (Ar : MeasSubcat R) : Type :=
  MkComonad {
  cm_obj  : ICone.type Ar -> ICone.type Ar;
  cm_fmap : forall B C, icones_hom Ar B C ->
                       icones_hom Ar (cm_obj B) (cm_obj C);
  cm_der  : forall B, icones_hom Ar (cm_obj B) B;
  cm_dig  : forall B, icones_hom Ar (cm_obj B) (cm_obj (cm_obj B));
  cm_fmap_id   : (* functor identity *) _;
  cm_fmap_comp : (* functor composition *) _;
  cm_counitL   : forall B,
    icones_comp (cm_der (cm_obj B)) (cm_dig B) = icones_id Ar (cm_obj B);
  cm_counitR   : forall B,
    icones_comp (cm_fmap (cm_der B)) (cm_dig B) = icones_id Ar (cm_obj B);
  cm_coassoc   : forall B,
    icones_comp (cm_dig (cm_obj B)) (cm_dig B) =
    icones_comp (cm_fmap (cm_dig B)) (cm_dig B);
}.

Definition Bang_comonad (R : realType) (Ar : MeasSubcat R) : Comonad Ar :=
  {| cm_obj := @Bang R Ar;
     cm_fmap := @bang_fmap R Ar;
     cm_der  := @der R Ar;
     cm_dig  := @dig R Ar;
     (* ... functor and comonad-law witnesses ... *) |}.
```

### Lem 9.4 (`stab_lin_swap`)

The *stable/linear swap* isomorphism exchanges a stable outer argument and a linear inner one: $(B \Rightarrow (C \multimap D)) \simeq (C \multimap (B \Rightarrow D))$, natural in $B$, $C$, $D$, sending $f$ to $\boldsymbol\lambda y\in\underline{C}\cdot\boldsymbol\lambda x\in\mathcal{B}\underline{B}\cdot f(x,y)$. It is the key ingredient in deriving the binary Seely iso. The paper gives only the map and calls the verification "a pattern seen many times"; the formalization spells out both directions and the cancellation proofs as a full `icones_iso`.

> **Paper — Lemma 9.4** (arXiv 2212.02371, `lemma:stab-lin-swap`). Let $B,C,D$ be integrable cones. There is an isomorphism in $\mathbf{ICones}$ from $L(B,C,D)=(B\Rightarrow(C\multimap D))$ to $R(B,C,D)=(C\multimap(B\Rightarrow D))$ which is natural in $B$, $C$ and $D$. The natural isomorphism maps $f\in\underline{B\Rightarrow(C\multimap D)}$ to $\boldsymbol\lambda y\in\underline{C}\cdot\boldsymbol\lambda x\in\mathcal{B}\underline{B}\cdot f(x,y)$.

```coq
(* theories/stable/stab_lin_swap.v — Section variables B C D : ICone.type Ar *)

Definition stab_lin_swap :
    icones_iso Ar (stablehom B (linhom_car Ar C D))
                  (linhom_car Ar C (stablehom B D)) :=
  icones_iso_of_cancel sls_fwd sls_bwd sls_fwdK sls_bwdK.

Lemma stab_lin_swap_fwdE (f : stablehom B (linhom_car Ar C D))
                         (y : C) (x : B) :
  sh_fun (linhom_fun (iso_fwd stab_lin_swap f) y) x =
  linhom_fun (sh_fun f x) y.

Lemma stab_lin_swap_bwdE (g : linhom_car Ar C (stablehom B D))
                         (x : B) (y : C) :
  linhom_fun (sh_fun (iso_bwd stab_lin_swap g) x) y =
  sh_fun (linhom_fun g y) x.
```

### Thm 9.5 (`Seely2`, `Seely2E`, `Seely2_natural`, `Seely0`, `Seely0E`, `SeelyCategory`, `ICones_Seely`)

Equipped with the strong monoidal comonad $!$, the SMCC $\mathbf{ICones}$ is a **Seely category**. Concretely, there are natural isos $\mathsf{m}^2_{B_1,B_2} : {!B_1}\otimes{!B_2}\simeq{!(B_1\mathrel{\&}B_2)}$ characterised by $\mathsf{m}^2_{B_1,B_2}(x_1^!\otimes x_2^!)=\langle x_1,x_2\rangle^!$, and $\mathsf{m}^0 : 1\simeq{!\top}$ characterised by $\mathsf{m}^0(t)=t\cdot 0^!$, together with the required comonad / SMC coherence diagrams. The `SeelyCategory` record bundles the SMCC, the comonad, the two Seely isos with their characterisations and naturality, and the coherence witnesses; `ICones_Seely` is the canonical, axiom-free instance.

> **Paper — Theorem 9.5** (arXiv 2212.02371). Equipped with the strong monoidal comonad $!$, the category $\mathbf{ICones}$ is a Seely category in the sense of Melliès.

> **Paper — §9** (arXiv 2212.02371, `sec:lin-nonlin-adj`). There is a natural isomorphism $\mathsf{m}^2_{B_1,B_2}$ in $\mathbf{ICones}({!B_1}\otimes{!B_2},{!(B_1\mathrel{\&}B_2)})$ which satisfies $\mathsf{m}^2_{B_1,B_2}(x_1^!\otimes x_2^!)=\langle x_1,x_2\rangle^!$ (this equation fully characterizes $\mathsf{m}^2_{B_1,B_2}$ by Lemma 9.2). Similarly we define an iso $\mathsf{m}^0\in\mathbf{ICones}(1,{!\top})$ such that $\mathsf{m}^0(t)=t\,0^!$ for all $t\in\mathbb{R}_{\geq 0}$.

```coq
(* theories/homs/seely.v *)

Definition Seely2 : icones_iso Ar (tensor Ar (Bang Ar B1) (Bang Ar B2))
                                   (Bang Ar (sprod B1 B2)) :=
  icones_isoP S2fwd S2bwd S2_fwdK S2_bwdK.

Lemma Seely2E (x1 : B1) (x2 : B2) :
  cone_norm x1 <= 1 -> cone_norm x2 <= 1 ->
  iso_fwd Seely2 (x1! ⊗p x2!) = (sprod_pair x1 x2)!.

Lemma Seely2_natural (B1 B2 B1' B2' : ICone.type Ar)
    (f1 : icones_hom Ar B1 B1') (f2 : icones_hom Ar B2 B2') :
  icones_comp (bang_fmap (sprod_mor f1 f2)) (iso_fwd (Seely2 B1 B2)) =
  icones_comp (iso_fwd (Seely2 B1' B2'))
              (tensor_mor (bang_fmap f1) (bang_fmap f2)).

Definition Seely0 : icones_iso Ar (cone_one_car Ar) (Bang Ar (Stop Ar)) :=
  co_yoneda_iso psi0 psiV0 psi0K psiV0K psi0_nat psiV0_nat.

Lemma Seely0E (t : cone_one_car Ar) :
  iso_fwd Seely0 t =
  precone_scale (c1_val t) (prom (precone_zero : Stop Ar)).

Record SeelyCategory (R : realType) (Ar : MeasSubcat R) : Type :=
  MkSeelyCategory {
  sc_smcc       : ICones_SMCC Ar;
  sc_comonad    : Comonad Ar;
  sc_bangE      : cm_obj sc_comonad = @Bang R Ar;
  sc_tensorE    : forall A B, smcc_tensor sc_smcc A B = tensor Ar A B;
  sc_seely2     : forall B1 B2, icones_iso Ar _ (Bang Ar (sprod B1 B2));
  sc_seely2E    : (* characterisation on promoted pure tensors *) _;
  sc_seely2_nat : (* naturality of Seely2 *) _;
  sc_seely0     : icones_iso Ar (cone_one_car Ar) (Bang Ar (Stop Ar));
  sc_seely0E    : (* characterisation of Seely0 *) _;
  sc_assoc sc_braid sc_lunit sc_runit : (* SMC functor coherence *) _;
  sc_comult     : (* comultiplication coherence *) _;
  sc_der_unit sc_der1 sc_der2 : (* counit compatibility *) _;
}.

Definition ICones_Seely (R : realType) (Ar : MeasSubcat R) :
    SeelyCategory Ar :=
  {| sc_smcc       := ICones_smcc Ar;
     sc_comonad    := Bang_comonad Ar;
     sc_bangE      := erefl;
     sc_tensorE    := fun _ _ => erefl;
     sc_seely2     := @Seely2 R Ar;
     sc_seely2E    := @Seely2E R Ar;
     sc_seely2_nat := @Seely2_natural R Ar;
     sc_seely0     := @Seely0 R Ar;
     sc_seely0E    := @Seely0E R Ar;
     (* ... structural-iso / coherence / counit witnesses ... *) |}.
```

### Thm 9.7 (`Coalg`, `Coalg_dirac`, `dirac_dense`, `FMeas_coalgebra`, `FMeas_fmap`)

For each $X\in\mathbf{Ar}$, the finite-measure cone $\mathsf{FMeas}(X)$ carries a $!$-coalgebra structure $\mathsf{h}_X\in\mathbf{ICones}(\mathsf{FMeas}(X),{!\mathsf{FMeas}(X)})$, defined via Theorem 6.1 as the integral of the Dirac path composed with the universal nonlinear map, so $\mathsf{h}_X(\mu)=\int_{r\in X}(\boldsymbol\delta^X(r))^!\,\mu(dr)$ and $\mathsf{h}_X(\boldsymbol\delta^X(r))=(\boldsymbol\delta^X(r))^!$. The coalgebra laws follow because the two sides agree on all Dirac measures (`dirac_dense`, paper Theorem 6.2), which are norm-dense. The assignment $X\mapsto\mathsf{FMeas}(X)$ then extends to a functor $\mathbf{Ar}\to\mathbf{ICones}^!$ acting on morphisms by pushforward $\mathsf{FMeas}(\phi)=\phi_\ast$.

> **Paper — Theorem 9.7** (arXiv 2212.02371, `th:meas-cone-coalgebra-stab`). Equipped with $\mathsf{h}_X$, the object $\mathsf{FMeas}(X)$ of $\mathbf{ICones}$ is a coalgebra of the comonad ${!}\_$. Moreover for each $\phi\in\mathbf{Ar}(X,Y)$, we have $\mathsf{FMeas}(\phi)=\phi_\ast\in\mathbf{ICones}^!(\mathsf{FMeas}(X),\mathsf{FMeas}(Y))$ so that $\mathsf{FMeas}$ is a functor $\mathbf{Ar}\to\mathbf{ICones}^!$.

> **Paper — §9** (arXiv 2212.02371, `sec:stable-exp-meas-coalg`). We define $\mathsf{h}_X=\mathcal{I}^{{!\mathsf{FMeas}(X)}}_X(\mathsf{nl}_{\mathsf{FMeas}(X)}\circ\boldsymbol\delta^X)\in\mathbf{ICones}(\mathsf{FMeas}(X),{!\mathsf{FMeas}(X)})$ using Theorem 6.1. In other words $\mathsf{h}_X(\mu)=\int_{r\in X}(\boldsymbol\delta^X(r))^!\,\mu(dr)$ and it satisfies $\mathsf{h}_X(\boldsymbol\delta^X(r))=(\boldsymbol\delta^X(r))^!$.

```coq
(* theories/homs/coalgebra.v *)

Record Coalgebra : Type := MkCoalgebra {
  coalg_obj    : ICone.type Ar;
  coalg_str    : icones_hom Ar coalg_obj (Bg coalg_obj);
  coalg_counit :
    icones_comp (der coalg_obj) coalg_str = icones_id Ar coalg_obj;
  coalg_coassoc :
    icones_comp (dig coalg_obj) coalg_str =
    icones_comp (bang_fmap coalg_str) coalg_str;
}.

Definition Coalg (X : ar_obj Ar) :
    icones_hom Ar (FMeas X) (Bang Ar (FMeas X)) :=
  linhom_icones (int_to_linhom (bang_dirac_path X)) (Coalg_norm_le1 X).

Lemma Coalg_dirac (X : ar_obj Ar) (r : ar_carrier Ar X) :
  Lfun (Coalg X) (dirac_fmeas r) = prom (dirac_fmeas r).

Lemma dirac_dense (X : ar_obj Ar) (B : ICone.type Ar)
    (f g : icones_hom Ar (FMeas X) B) :
  (forall r, Lfun f (dirac_fmeas r) = Lfun g (dirac_fmeas r)) ->
  f = g.

Definition FMeas_coalgebra (X : ar_obj Ar) : Coalgebra Ar :=
  MkCoalgebra (Coalg_counit X) (Coalg_coassoc X).

Definition FMeas_fmap (X Y : ar_obj Ar) (φ : ar_hom Ar X Y) :
    icones_hom Ar (FMeas X) (FMeas Y) :=
  linhom_icones (int_to_linhom (push_dirac_path φ)) (FMeas_fmap_norm_le1 φ).
```

---

## Beyond the paper — paper-cited meta-theorems we mechanised in full

The paper *cites* a number of categorical / linear-logic results as black
boxes (SAFT, Lack's lifting, Mellies §7.4 Prop 28 / Cor 20 / Prop 29) which
a textbook reader can take on trust. A machine-checked development cannot
cite a black box; the following constructions are real mathematical content
the formalisation adds *to discharge the paper's citations*. Each is
justified by an external reference (Riehl, Mellies).

The PPL-side beyond-the-paper content (Boolean cascade, CBV value-fixpoint,
the surface language and its examples) is in the [PPL tab](../ppl/).

### Mechanisation of the Special Adjoint Functor Theorem (paper §4.3, §5, §7, §9)

The paper builds `⊗`, `!`, and the Seely isos via Freyd's SAFT (Riehl,
*Category Theory in Context* Thm 4.6.10 / Cor 4.6.14) — a complete,
well-powered category with a coseparator has a left adjoint to every
continuous functor. Rather than postulate SAFT, we **mechanise the SAFT
argument concretely**: the left adjoint of `F` at `c` is the (wide)
intersection of the subobjects of a power of the coseparator `1` over which
`c → F-` factors.

| Construction | Rocq |
|---|---|
| Subobject classifier on `ICones` (Thm 4.18 fully proved, not stubbed) | `SubobjClassifier`, `icones_subobject_classP`, `icones_well_powered` — `theories/icones/representable.v` |
| Binary intersection (pullback) of subobjects + UMP | `pb_med`, `pb_med_proj1/2`, `pb_med_unique` — same file |
| Wide intersection of a small family of subobjects + cone UMP | `wi_obj`, `wi_med`, `wi_med_proj`, `wi_med_unique` — same file |
| Initiality engine (intersection embeds in each member; mono if members are) | `wi_factors_each`, `wi_incl_inj` — same file |
| Export contract: hom-bijection a left-adjoint candidate must satisfy | `is_icones_left_adjoint` — same file |

#### Code

```coq
(* theories/icones/representable.v *)

(** Binary intersection of two subobjects (pullback) and its UMP. *)
Definition pb_med : icones_hom Ar Z pb_obj :=
  icones_eq_med pb_left pb_right pb_tuple pb_tuple_equ.

Lemma pb_med_proj1 : icones_comp pb_proj1 pb_med = f.
Lemma pb_med_proj2 : icones_comp pb_proj2 pb_med = g.

Lemma pb_med_unique (k : icones_hom Ar Z pb_obj) :
  icones_comp pb_proj1 k = f ->
  icones_comp pb_proj2 k = g ->
  k = pb_med.

(** Wide intersection of a small family of subobjects: object, embedding,
    projections, and the mediator + factor + uniqueness for any cone. *)
Definition wi_obj  : ICone.type Ar := icones_eq wi_u wi_v.
Definition wi_incl : icones_hom Ar wi_obj p :=
  icones_comp (icones_comp (hh k0) (wi_pi k0)) (icones_eq_incl wi_u wi_v).
Definition wi_proj (k : K) : icones_hom Ar wi_obj (Adom k) :=
  icones_comp (wi_pi k) (icones_eq_incl wi_u wi_v).

Definition wi_med : icones_hom Ar Z wi_obj :=
  icones_eq_med wi_u wi_v wi_tuple wi_tuple_equ.

Lemma wi_med_proj (k : K) : icones_comp (wi_proj k) wi_med = ff k.
Lemma wi_med_unique (kk : icones_hom Ar Z wi_obj) :
  (forall k, icones_comp (wi_proj k) kk = ff k) -> kk = wi_med.

(** Initiality: the intersection factors each member, and the embedding
    is a mono if the basepoint member and own projection are monos. *)
Lemma wi_factors_each (k : K) :
  icones_comp (hh k) (wi_proj Adom hh k0 k) = wi_incl Adom hh k0.
Lemma wi_incl_inj :
  is_icones_inj (hh k0) ->
  is_icones_inj (wi_proj Adom hh k0 k0) ->
  is_icones_inj (wi_incl Adom hh k0).

(** The SAFT export contract — a left-adjoint candidate is a hom-bijection. *)
Definition is_icones_left_adjoint
    (Cobj : Type) (Homc : Cobj -> Cobj -> Type)
    (Robj : ICone.type Ar -> Cobj)
    (Fobj : Cobj -> ICone.type Ar)
    (Phi : forall (c : Cobj) (x : ICone.type Ar),
             icones_hom Ar (Fobj c) x -> Homc c (Robj x))
    (Psi : forall (c : Cobj) (x : ICone.type Ar),
             Homc c (Robj x) -> icones_hom Ar (Fobj c) x) : Prop :=
  (forall c x (f : icones_hom Ar (Fobj c) x), Psi c x (Phi c x f) = f) /\
  (forall c x (g : Homc c (Robj x)), Phi c x (Psi c x g) = g).
```

The tensor `⊗` and the exponential `!` are then **discharged** against this
SAFT engine:

| What | Rocq |
|---|---|
| `−⊗C` is the SAFT left adjoint of `(C⊸−)` (Thm 5.9 + the SAFT engine) | `tensor_construct.v` (the tensor itself + curry/uncurry + naturality) — `theories/homs/tensor_construct.v` |
| The Thm 5.12 measurability core (the analytic crux) | `tensor_hom_iso.v` + `tensor_iso.v` (the `path_tens_to_X` / `lfun_path_swap` / `swap_lin_lin_hom` chain) |
| `E` is the SAFT left adjoint of `Der` (Thm 7.34 feeding the SAFT engine) | `der_continuous.v` (Thm 7.34) + `bang_construct.v` (Bang/nl/lin discharged) |
| The Seely isos (Thm 9.5) are discharged via Lem 9.4 + tensor-hom-iso | `theories/stable/stab_lin_swap.v` + the construction in `seely.v` |

#### Code: tensor and exponential as SAFT left adjoints

```coq
(* theories/homs/tensor_construct.v *)
Module Icones_tensor_construct.
(* ... family of factoring subobjects of the product p = (C ⊸ −),
   indexed by the well-powered classifier ... *)

(** The tensor object [B ⊗ C] as the wide intersection of the family. *)
Definition tensor : ICone.type Ar := wi_obj fhh fk0.

(** The intersection embedding [B ⊗ C ↪ p]. *)
Definition tensor_incl : icones_hom Ar tensor p := wi_incl fAdom fhh fk0.

(* ... + curry / uncurry / naturality, the SAFT discharge ... *)
End Icones_tensor_construct.
```

```coq
(* theories/homs/bang_construct.v *)
Module Icones_bang_construct.

(** The exponential object [Bang B = E B] as the wide intersection of
    the family of factoring subobjects of [B ⊸ 1ᴬ]. *)
Definition Bang : ICone.type Ar := wi_obj fhh fk0.
Definition Bang_incl : icones_hom Ar Bang p := wi_incl fAdom fhh fk0.

(** The universal nonlinear map [nl_B]. *)
Definition nl : scones_hom B (Bang B) := (* ... *).

(** The linear factoriser [lin f]. *)
Definition lin : icones_hom Ar (Bang B) C := (* ... *).

End Icones_bang_construct.
```

The strategy is the paper's (§4.3 explicitly invokes SAFT); the formalisation
adds the *concrete* SAFT construction so the tree carries no `Parameter` /
`Axiom` interfaces and the whole development is axiom-free.

### EM(!) is fully cartesian — Mellies §7.4 Prop 28 / Cor 20

Beyond §9, the formalisation also delivers Mellies' result that the
Eilenberg–Moore category of `!` (the value category of a linear-logic CBV
interpretation) is cartesian, with product carried by the linear `⊗`
(not the cartesian `&`). The non-trivial part is **Cor 20**, the step
Mellies himself flags as *"does not seem to follow from general abstract
properties"*: the transported comonoid diagonal must be shown to be a
coalgebra morphism, on *every* coalgebra.

| Lemma | English statement | Rocq |
|---|---|---|
| Mellies Prop 26 | Every coalgebra `(A,a)` is a retract of its cofree `(!A, dig)` in `EM(!)`. | `diagram81` (records the key Eq 88 retraction-square) — `theories/homs/em_cartesian.v` |
| Mellies §6.11 Prop 20 / Cor 20 | If `i` is a coalgebra morphism with a carrier retraction `r∘i = id` and `i∘f` is a coalgebra morphism, then `f` is. | `coalg_mor_lift` (the diagram (66)/(67) chase Mellies flags as *"not so immediate"*) — same file |
| Mellies Prop 27 (transport) | A retract of a commutative comonoid is a commutative comonoid. | The four transported laws (`transp_counitL/_R/_cocomm/_coassoc`) — same file |
| Mellies Prop 28 | `EM(!)` is cartesian on **every** coalgebra (`EMComon` holds unconditionally). | `EMComon_all : forall P : Coalgebra Ar, EMComon P` — same file |
| Mellies Cor 17 | A symmetric monoidal category in which every object has a natural commutative comonoid is cartesian. | The headline `ICones_EM_cartesian` (with `cart_prod`, `cart_term`, the projections, pairing, β-laws) — same file |

The naïve approach — reducing to *promoted points* `x!` via `d_bang_prom`
— cannot work for a general carrier (an arbitrary `a x` is not promoted).
The structural retraction proof is what Mellies' §7.4 actually requires;
it is mechanised here.

#### Code

```coq
(* theories/homs/em_cartesian.v *)

(** Eq (88) of Mellies: the retraction square for an arbitrary coalgebra. *)
Lemma diagram81 (P : Coalgebra Ar) :
  icones_comp (tensor_mor (coalg_str P) (coalg_str P)) (coalg_d P) =
  icones_comp (d_bang (coalg_obj P)) (coalg_str P).

(** Mellies §6.11 Prop 20 / Cor 20 — the (66)/(67) diagram chase that
    Mellies flags as "not so immediate". *)
Lemma coalg_mor_lift (X PA QB : Coalgebra Ar)
    (i : icones_hom Ar (coalg_obj PA) (coalg_obj QB))
    (r : icones_hom Ar (coalg_obj QB) (coalg_obj PA))
    (f : icones_hom Ar (coalg_obj X) (coalg_obj PA)) :
  is_coalg_mor PA QB i ->
  icones_comp r i = icones_id Ar (coalg_obj PA) ->
  is_coalg_mor X QB (icones_comp i f) ->
  is_coalg_mor X PA f.

(** Mellies Prop 27 (transported comonoid laws on a retract).  Section
    variables fix the [(i, r, dB, eB)] retraction setup and an Eq-(85)
    hypothesis. *)
Lemma transp_counitL :
  icones_comp (iso_fwd (tensor_lunit A))
    (icones_comp (tensor_mor eA (icones_id Ar A)) dA) = icones_id Ar A.

Lemma transp_counitR :
  icones_comp (iso_fwd (tensor_runit A))
    (icones_comp (tensor_mor (icones_id Ar A) eA) dA) = icones_id Ar A.

Lemma transp_cocomm :
  icones_comp (iso_fwd (tensor_braid A A)) dA = dA.

Lemma transp_coassoc :
  icones_comp (iso_fwd (tensor_assoc A A A))
    (icones_comp (tensor_mor dA (icones_id Ar A)) dA) =
  icones_comp (tensor_mor (icones_id Ar A) dA) dA.

(** Mellies Prop 28 unconditionally on every coalgebra. *)
Lemma EMComon_all (P : Coalgebra Ar) : EMComon P.

(** Cor 17: the full EM(!) is cartesian, with product carried by ⊗. *)
Record EM_Cartesian (R : realType) (Ar : MeasSubcat R) : Type :=
  MkEMCartesian {
  cart_prod : Coalgebra Ar -> Coalgebra Ar -> Coalgebra Ar;
  cart_term : Coalgebra Ar;
  cart_prod_obj : forall P Q,
    coalg_obj (cart_prod P Q) = tensor Ar (coalg_obj P) (coalg_obj Q);
  cart_proj1 : forall P Q,
    icones_hom Ar (coalg_obj (cart_prod P Q)) (coalg_obj P);
  cart_proj2 : forall P Q,
    icones_hom Ar (coalg_obj (cart_prod P Q)) (coalg_obj Q);
  cart_pair : forall (Z P Q : Coalgebra Ar),
    coalg_hom Z P -> coalg_hom Z Q -> coalg_hom Z (cart_prod P Q);
  cart_beta1 : (* β law on proj1 *) _;
  cart_beta2 : (* β law on proj2 *) _;
  cart_term_mor    : forall P, coalg_hom P cart_term;
  cart_term_unique : (* terminal UP *) _;
}.

(** The canonical cartesian structure of EM(!), every field populated. *)
Definition ICones_EM_cartesian (R : realType) (Ar : MeasSubcat R) :
    EM_Cartesian Ar :=
  {| cart_prod := @EM_prod R Ar;
     cart_term := @EM_term R Ar;
     cart_prod_obj := @EM_prod_obj R Ar;
     cart_proj1 := @em_proj1_mor R Ar;
     cart_proj2 := @em_proj2_mor R Ar;
     cart_pair := fun Z P Q f g => @em_pair R Ar Z P Q f g;
     (* ... β-laws and terminal UP witnesses ... *) |}.
```

### Cartesian-η of EM(!)

The β-laws `em_proj1_pair` / `em_proj2_pair` of the previous section establish
the universal property of the EM(!) binary product *out of* a coalgebra `Z`;
they do not by themselves say `⟨π₁, π₂⟩ = id`. The η-law is genuinely
additional content — it is **Fox's 1976 theorem** specialised to EM(!) of a
linear-exponential comonad (Melliès Proposition 28 at the icones level).
It is proved here in the same style as Cor 20: by Melliès's
retract-and-lift technique, *not* by promoted-point reduction.

| Lemma | English statement | Rocq |
|---|---|---|
| Cofree case | On the cofree pair `(!̃A, !̃B)` the η-law `em_pair_mor π₁ π₂ = id` reduces, via `tens_excl_charact`, to a computation on the promoted tensor `x! ⊗ y!`. | `em_pair_mor_proj_id_cofree` — `theories/programs/infra/cbv_adjunction.v` |
| Full η-law | For every pair `(P, Q)` of coalgebras, `em_pair_mor π₁ π₂ = id_{cP⊗cQ}` on the underlying carriers. Proved by the split-mono retraction `coalg_str P ⊗ coalg_str Q ⊣ der_cP ⊗ der_cQ` reducing the equation to the cofree case. | `em_pair_mor_proj_id` — same file |

#### Code

```coq
(* theories/programs/infra/cbv_adjunction.v *)

(** The cofree case: η reduces on promoted tensors. *)
Lemma em_pair_mor_proj_id_cofree (A B : ICone.type Ar) :
  @em_pair_mor R Ar (EM_prod (bang_cofree A) (bang_cofree B))
    (bang_cofree A) (bang_cofree B)
    (em_proj1_mor (bang_cofree A) (bang_cofree B))
    (em_proj2_mor (bang_cofree A) (bang_cofree B))
  = icones_id Ar (coalg_obj (EM_prod (bang_cofree A) (bang_cofree B))).

(** The full cartesian η-rule on every coalgebra. *)
Lemma em_pair_mor_proj_id (P Q : Coalgebra Ar) :
  @em_pair_mor R Ar (EM_prod P Q) P Q
    (em_proj1_mor P Q) (em_proj2_mor P Q)
  = icones_id Ar (tensor Ar (coalg_obj P) (coalg_obj Q)).
```

### Linear/non-linear monoidal adjunction `U ⊣ !̃` (Mellies §7.4 Prop 29)

| Result | English statement | Rocq |
|---|---|---|
| LNL adjunction | The cofree-coalgebra adjunction `U ⊣ !̃ : ICones ⇄ EM(!)` is a lax symmetric monoidal adjunction (Lack's lifting). With Cor 20 in hand, this is a genuine *linear/non-linear* adjunction with the **full** category of `!`-coalgebras as the cartesian non-linear / value side. | `CBV_Model` record + `ICones_CBV` witness — `theories/programs/infra/cbv_adjunction.v` |

#### Code

```coq
(* theories/programs/infra/cbv_adjunction.v *)

(** The Melliès §7.4 Prop 29 monoidal adjunction U ⊣ !̃ bundled.
    Fields cover: the (Thm 5.15) SMCC of ICones, the EM(!) category,
    the (full) cartesian value category EM_Cartesian, the U / !̃
    object and morphism actions, the unit / counit / Φ / Ψ / triangle
    identities, the U strict-monoidal compatibility, and the !̃ lax
    symmetric monoidal comparison + lax coherence + (co)unit
    monoidality. *)
Record CBV_Model (R : realType) (Ar : MeasSubcat R) : Type := MkCBVModel {
  cbv_smcc : ICones_SMCC Ar;
  cbv_em   : EM_Cat Ar;
  cbv_cart : EM_Cartesian Ar;

  cbv_U_obj    : Coalgebra Ar -> ICone.type Ar;
  cbv_U_mor    : forall P Q, coalg_hom P Q ->
                             icones_hom Ar (cbv_U_obj P) (cbv_U_obj Q);
  cbv_bang_obj : ICone.type Ar -> Coalgebra Ar;
  cbv_bang_mor : forall B C, icones_hom Ar B C ->
                             coalg_hom (cbv_bang_obj B) (cbv_bang_obj C);
  cbv_unit     : forall P, coalg_hom P (cbv_bang_obj (cbv_U_obj P));
  cbv_counit   : forall B, icones_hom Ar (cbv_U_obj (cbv_bang_obj B)) B;
  cbv_phi      : forall P B,
    coalg_hom P (cbv_bang_obj B) -> icones_hom Ar (cbv_U_obj P) B;
  cbv_psi      : forall P B,
    icones_hom Ar (cbv_U_obj P) B -> coalg_hom P (cbv_bang_obj B);
  cbv_phiK : (* Φ ∘ Ψ = id *) _;
  cbv_psiK : (* Ψ ∘ Φ = id *) _;
  cbv_triangleL : (* triangle on the unit *) _;
  cbv_triangleR : (* triangle on the counit *) _;

  (* U strict / strong monoidal *)
  cbv_U_prod : forall P Q, cbv_U_obj (cart_prod cbv_cart P Q) =
                            tensor Ar (cbv_U_obj P) (cbv_U_obj Q);
  cbv_U_term : cbv_U_obj (cart_term cbv_cart) = cone_one_car Ar;

  (* !̃ lax symmetric monoidal: m2 / m0 comparisons (as ICones maps and
     as EM(!) morphisms), the lax coherence (assoc, braid), and the
     counit-monoidality laws. *)
  cbv_m2 : forall A B, icones_hom Ar _ (cbv_U_obj (cbv_bang_obj (tensor Ar A B)));
  cbv_m0 : icones_hom Ar (cone_one_car Ar) (cbv_U_obj (cbv_bang_obj (cone_one_car Ar)));
  cbv_bang_m  : forall A B,
    coalg_hom (cart_prod cbv_cart (cbv_bang_obj A) (cbv_bang_obj B))
              (cbv_bang_obj (tensor Ar A B));
  cbv_bang_e0 : coalg_hom (cart_term cbv_cart) (cbv_bang_obj (cone_one_car Ar));
  cbv_lax_assoc : _; cbv_lax_braid : _;
  cbv_counit_monoidal2 : _; cbv_counit_monoidal0 : _;
}.

(** Paper-style headline: every field populated by a proved lemma. *)
Definition ICones_CBV (R : realType) (Ar : MeasSubcat R) : CBV_Model Ar :=
  {| cbv_smcc := ICones_smcc Ar;
     cbv_em   := ICones_EM Ar;
     cbv_cart := ICones_EM_cartesian Ar;
     cbv_U_obj := @U_obj R Ar;
     cbv_U_mor := @U_mor R Ar;
     (* ... !̃ / unit / counit / triangle / lax-monoidal witnesses ... *) |}.
```

## What is **not** formalised

These are paper sections we have not (yet) formalised. The choices are
deliberate; each requires substantial infrastructure outside the current
scope.

| Paper | What it is | Why not yet |
|---|---|---|
| § 8 | *Analytic* functions, the cartesian closed `ACONES`; the analytic exponential `!ₐ`. | A separate analytic layer (radius-of-convergence, complex analyticity, Taylor expansions of stable functions) is required. |
| § 9 (post-9.7) | The full-subcategory theorem: for Polish / standard-Borel `X`, `FMeas(X) ↪ EM(!)` is full. | Requires a Polish / standard-Borel layer in mathcomp-analysis and two folklore measure-theoretic lemmas (regularity of finite Borel measures, image-measure determination); not yet in inventory. |
| § 10 | Embedding into probabilistic coherence spaces. | Requires a separate PCS formalisation. |

---

## How to verify the development for yourself

```sh
# 1. Clone and build (Rocq 9.1.1 + mathcomp-analysis 1.16).
opam install --deps-only ./icones.opam
make -j

# 2. Run the axiom-budget check on the regression anchor.
./verify.sh

# 3. Spot-check any headline result yourself.
echo 'From Icones.homs Require Import seely. Print Assumptions Icones.homs.seely.ICones_Seely.' \
  | rocq top -Q theories Icones

# Or for the higher-order PPL example:
echo 'From Icones.programs Require Import ppl. Print Assumptions Icones.programs.ppl.ex_random_linear_denot_E.' \
  | rocq top -Q theories Icones
```

In each case the only axioms printed should be the three classical-logic
axioms `propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`. No project-specific axiom should
appear, and there are no `Admitted` proofs in `theories/`.

A short tour for a paper reviewer who wants to verify the headline paper
results:

1. **Theorem 6.5** (`Skern_to_ICones_fully_faithful` in
   `theories/kernels/kernel_embedding.v`) — the embedding theorem; the
   regression anchor of the whole tree.
2. **Theorem 5.15** (`ICones_smcc` in `theories/homs/smcc.v`) — the linear
   logic core: `(ICones, ⊗, 1)` is a SMCC.
3. **Theorem 7.32** (`SCones_ccc` in `theories/stable/scones_ccc.v`) — the
   cartesian closed `SCones`.
4. **Theorem 9.5** (`ICones_Seely` in `theories/homs/seely.v`) — the Seely
   category structure (the full LL / intuitionistic-linear model).
5. **Theorem 9.7** (`FMeas_coalgebra` in `theories/homs/coalgebra.v`) — the
   measure cone is a `!`-coalgebra; `X ↦ FMeas(X)` is a functor into `EM(!)`.
6. **The mechanised paper-cited meta-theorems** (`EMComon_all` and
   `ICones_CBV` in `theories/homs/em_cartesian.v` /
   `theories/programs/infra/cbv_adjunction.v`) — Mellies' Cor 20 (full
   cartesianness of `EM(!)`) and the LNL adjunction.

For the PPL development on top — including recursive examples and their
mass identities — see the [PPL tab](../ppl/).

For deeper inspection, the `blueprint/` directory contains a
LaTeX/Patrick-Massot-style overview that mirrors this table chapter by
chapter, with clickable links to each Rocq definition.
