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
echo 'Print Icones.exp.seely.ICones_Seely.' | rocq top -Q theories Icones

# Axiom dependencies
echo 'Print Assumptions Icones.exp.seely.ICones_Seely.' \
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
| Lem 2.9 | Addition and scalar multiplication on a cone are increasing and $\omega$-continuous. | `addr_omega_continuous`, `addl_omega_continuous`, `scaler_omega_continuous` — `theories/cones/basic_lemmas.v` |
| Lem 2.8 / 2.10 | $\omega$-continuity of the inverse of a bijective linear continuous map / of the difference $g - f$ of an increasing $f$ below an $\omega$-continuous $g$. | `invf_omega_continuous`, `diff_omega_continuous` — `theories/cones/basic_lemmas.v` |
| Lem 2.11 | A linear map is bounded on the unit ball; the operator norm $\lVert f\rVert$. | `linmap_bounded`, `linmap_norm` — `theories/cones/basic_lemmas.v` |
| Thm 2.18 | $\mathbf{Cones}$ has all small products $\mathop{\&}_{i\in I}P_i$ (terminal object $\top$ at $I=\emptyset$). | `cones_prod`, `cones_proj`, `cones_tuple` — `theories/cones/cone_cat.v` |
| Lem 2.19 | Separate $\omega$-continuity implies joint $\omega$-continuity (diagonal-collapse form). | `diagonal_collapse` — `theories/cones/cone_cat.v` |
| Thm 2.20 | $\mathbf{Cones}$ has all binary equalisers, hence is complete; the inclusion reflects the order. | `cones_eq`, `cones_eq_incl`, `cones_eq_med` — `theories/cones/cone_cat.v` |
| Lem 2.21 / Prop 2.22 | An iso in $\mathbf{Cones}$ preserves the norm exactly (constructive form of $\lVert f\rVert=1$). | `cones_iso_preserves_norm` — `theories/cones/cone_cat.v` |
| Lem 2.23 | Transport of a cone structure along a bijection. | `transport_isPrecone` — `theories/cones/cone_cat.v` |
| §2.3 ⊤ / ⊥ | The two constant example cones: the zero-dimensional $\top$ (a single element, $\lVert\cdot\rVert\equiv 0$, the terminal object) and the one-dimensional $\bot = \mathbf{1} = \mathbb{R}_{\geq 0}$ (norm $\lVert r\rVert = r$). | `ConeBot.T`, `ConeOne.T` — `theories/cones/examples_cone.v` |

Notable design choice: $\omega$-continuity comes in two flavours — `is_omega_continuous`
(input and output chains live in the unit ball; linear-tailored) and
`is_scott_continuous_unit` (input chain in the ball, output at any radius;
the *general* notion needed for non-linear stable maps in §7). Both are
proved equivalent for linear maps.

> **Prototype — paper §2.2 "An archetypal example: the cone of finite measures".** Every clause of Def 2.2 is shaped to capture one property of $\mathsf{FMeas}(X)$, the set of finite non-negative measures on a measurable space $X$: the algebraic operations are pointwise on measurable sets ($(\mu_1+\mu_2)(U)=\mu_1(U)+\mu_2(U)$), the norm is the total mass $\lVert\mu\rVert=\mu(X)$, the cone order $\mu_1\le\mu_2$ is the pointwise order $\forall U\in\sigma_X\,.\,\mu_1(U)\le\mu_2(U)$, and (Normc) holds because the least upper bound of a norm-bounded increasing sequence is computed pointwise, $\mu(U)=\sup_n\mu_n(U)$, and exists by monotone convergence. *Where it is formalised:* the cone (and then measurable-cone) structure on $\mathsf{FMeas}(X)$ is built in `theories/mcones/fmeas.v` and documented under **Def 3.16** below, because the Rocq file also installs the measurability structure; §2 states only the abstract axioms this example motivates.

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

> **Difference — the cone order is a `Prop` predicate, not an `Order.POrder` instance.** The cone order $x_1\le x_2\iff\exists z\,.\,x_2=x_1+z$ is `Prop`-valued and in general undecidable, so no `Order.POrder` structure is registered on `Precone`: doing so would force either a `bool` projection (which the existential forbids) or carrying the whole mathcomp order theory along ghost `Prop` arguments. The order is exposed instead as the plain predicate `precone_le` (notation `x <=p y` in `precone_scope`) with its own reflexivity / transitivity / antisymmetry lemmas, gathered in `Section PreconeOrder` of `precone.v`, together with the monotonicity / cancellation rewriting lemmas of the same section (`precone_add_le_r`, `precone_add_le_l`, `precone_le_addlI`, `precone_le0`, `precone_scale_le`); HB hierarchies are reserved for the algebraic and normed structure. Antisymmetry is a *derived* fact, proved from (Cancel) and (Pos) exactly as in the paper's §2.1 — it is not an axiom of `isPrecone` — and it is what makes the difference $x_2-x_1$ unique.

```coq
(* theories/cones/precone.v — Section PreconeOrder,
   Variables (R : realType) (P : preconeType R) *)
Definition precone_le (x y : P) : Prop := exists z : P, y = x + z.

Lemma precone_le_refl : forall x, precone_le x x.

Lemma precone_le_trans : forall y x z,
  precone_le x y -> precone_le y z -> precone_le x z.

Lemma precone_le_anti : forall x y,
  precone_le x y -> precone_le y x -> x = y.

Lemma precone_le0 x : precone_le 0 x.
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

> **Difference — the norm is valued in `R`, not `{nonneg R}`.** The paper's norm is $\lVert\cdot\rVert : P\to\mathbb{R}_{\geq 0}$. The `isCone` mixin instead takes `cone_norm : P -> R` for `R : realType` and recovers non-negativity as the derived lemma `cone_norm_ge0` (itself a one-line consequence of (Normp) at `precone_le0` together with `cone_norm0`). *Why:* a `{nonneg R}` codomain would force a `%:num` coercion into every arithmetic step of every downstream proof with no logical benefit, whereas keeping the norm in `R` matches mathcomp's own treatment of norms. The three facts a reader will look for are derived immediately from (Normh) and (Normp): `cone_norm0` ($\lVert 0\rVert = 0$), `cone_norm_ge0` ($\lVert x\rVert\geq 0$), and `cone_normz_iff`, the biconditional repackaging of (Normz). Throughout `theories/` the abbreviation `cnorm` stands for `cone_norm`.

> **Design note — why (Normc) is an *operator* and not a $\Sigma$-type.** The alternative encoding of "each bounded increasing chain has a lub" is a sigma-type field $\{x\mid\dots\}$ from which a sup is extracted by `cid` on demand. That was rejected: many §3–§7 proofs need the sup *as a function of the chain* — to argue that two chain-equivalences yield equal sups, or to rewrite under it — and re-extracting through `cid` at every use blocks exactly those rewriting steps in the $\omega$-continuity arguments. `cone_sup_ball` therefore takes the chain and its two hypotheses as explicit arguments, with `cone_sup_ball_ub` / `cone_sup_ball_lub` / `cone_sup_ball_norm` as separate characterising fields. The same choice is what lets §7 generalise the operator to an arbitrary radius (`cone_sup_at` of `theories/cones/omega_general.v`) instead of re-deriving it, and what lets the §2 continuity lemmas be stated as sup *identities* (e.g. $\sup_n(u_n+y)=(\sup_n u_n)+y$) rather than as existence claims.

```coq
(* theories/cones/cone.v — Section ConeLemmas,
   Variables (R : realType) (P : coneType R) *)
Lemma cone_norm0 : cnorm (precone_zero : P) = 0.

Lemma cone_norm_ge0 x : 0 <= cnorm x.

Lemma cone_normz_iff x : cnorm x = 0 <-> x = precone_zero.
```

### Cat 2 (`cones_hom`, `cones_comp`, `Cones`)

The category $\mathbf{Cones}$ has cones as objects; a morphism $P \to Q$ is a linear, $\omega$-continuous map with operator norm $\leq 1$. The norm-nonexpansiveness is encoded pointwise as $\lVert f(x)\rVert \leq \lVert x\rVert$, which is equivalent to $\lVert f\rVert\leq 1$.

> **Paper — Definition 2.17** (arXiv 2212.02371). The category $\mathbf{Cones}$ has the cones as objects, and $\mathbf{Cones}(P,Q)$ is the set of all linear and continuous $f:P\to Q$ such that $\lVert f\rVert\leq 1$.

> **Difference.** The paper's morphism condition $\lVert f\rVert\leq 1$ is the operator norm $\sup_{x\in\mathbf{B}P}\lVert f(x)\rVert\leq 1$; the formalization records the pointwise inequality `cones_hom_norm_le1` : $\forall x\, .\, \lVert f(x)\rVert\leq\lVert x\rVert$, which is equivalent but avoids materialising the supremum.

> **Design note — why the pointwise condition, and what it costs.** Paper Definition 2.17 phrases the morphism condition as $\lVert f\rVert\leq 1$ for the operator norm $\lVert f\rVert=\sup_{x\in\mathbf{B}P}\lVert f(x)\rVert$ (Lemma 2.11). The record field `cones_hom_norm_le1` instead says $\forall x,\ \lVert f(x)\rVert_Q\leq\lVert x\rVert_P$. The two are equivalent — one direction is immediate from (Normh), the other by applying the sup to a rescaling of $x$ — but the pointwise form does not materialise `linmap_norm` inside every `cones_hom`; and `linmap_norm` is *not* the supremum but a `cid`-extracted **upper bound** obtained from `linmap_bounded` (see the Difference note on Lemma 2.11), so a record field carrying it would bake a non-canonical choice into the morphism type. The operator norm stays available as a derived quantity wherever it is genuinely wanted.

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

The category laws are proved, not merely asserted: `cones_hom_eq` is the subtype-extensionality principle (two `cones_hom` records with pointwise-equal functions are equal, by `funext` plus `Prop`-irrelevance on the three proof fields), and the identity and associativity laws `cones_compIl` / `cones_compIr` / `cones_compA` all follow from it by direct calculation. `comp_norm_le1` is the closure fact that makes `cones_comp` well-defined: pointwise norm non-expansiveness composes.

```coq
(* theories/cones/cone_cat.v — Section ConesCat,
   Variables (R : realType) (P Q S T : coneType R) *)
Lemma cones_hom_eq (f g : cones_hom P Q) :
  (forall x, cones_hom_fun f x = cones_hom_fun g x) -> f = g.

Lemma comp_norm_le1 {g : Q -> S} {f : P -> Q} :
  (forall x, cone_norm (f x) <= cone_norm x) ->
  (forall y, cone_norm (g y) <= cone_norm y) ->
  forall x, cone_norm (g (f x)) <= cone_norm x.

Definition cones_id : cones_hom P P.

Lemma cones_compIl (P Q : coneType R) (f : cones_hom P Q) :
  cones_comp (cones_id Q) f = f.

Lemma cones_compIr (P Q : coneType R) (f : cones_hom P Q) :
  cones_comp f (cones_id P) = f.

Lemma cones_compA (P Q S T : coneType R)
  (h : cones_hom S T) (g : cones_hom Q S) (f : cones_hom P Q) :
  cones_comp h (cones_comp g f) = cones_comp (cones_comp h g) f.
```

### Lemma 2.9 (`addr_omega_continuous`, `addl_omega_continuous`, `scaler_omega_continuous`)

On any cone, both structural operations — addition $P\times P\to P$ and scalar multiplication $\mathbb{R}_{\geq 0}\times P\to P$ — are increasing and $\omega$-continuous. The $\omega$-continuity trio (`addr_omega_continuous`, `addl_omega_continuous`, `scaler_omega_continuous`) is the headline; the increasing halves are `addr_increasing`, `addl_increasing`, `scaler_increasing`.

> **Paper — Lemma 2.9** (arXiv 2212.02371, `content.tex:622`). Let $P$ be a cone. Addition $P\times P\to P$ and scalar multiplication $\mathbb{R}_{\geq 0}\times P\to P$ are increasing and $\omega$-continuous.

> **Difference.** The paper bundles addition and scalar multiplication into one lemma, each treated as a two-argument map. The mechanisation unbundles by argument — addition in the first argument (`addr_*`), addition in the second argument (`addl_*`), and scalar multiplication in the vector argument (`scaler_*`) — and separates the *increasing* halves (`*_increasing`) from the *$\omega$-continuous* halves (`*_omega_continuous`). The $\omega$-continuity is stated via the explicit `cone_sup_ball` least-upper-bound operator: e.g. $\sup_n(u_n+y)=(\sup_n u_n)+y$.

```coq
(* theories/cones/basic_lemmas.v — Section Lemma29,
   Variables R : realType, P : coneType R *)

Lemma addr_increasing y : is_increasing (fun x : P => precone_add x y).
Lemma addl_increasing x : is_increasing (fun y : P => precone_add x y).
Lemma scaler_increasing r : is_increasing (fun x : P => precone_scale r x).

Lemma addr_omega_continuous y :
  is_omega_continuous (fun x : P => precone_add x y).

Lemma addl_omega_continuous x :
  is_omega_continuous (fun y : P => precone_add x y).

Lemma scaler_omega_continuous (r : {nonneg R}) :
  is_omega_continuous (fun x : P => precone_scale r x).
```

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

The linearity half of paper Lemma 2.8 — which the Difference note above calls "a separate result in the same section" — is `invf_linear`, proved in the same `basic_lemmas.v` section from injectivity of `f` and its linearity; together with `invf_omega_continuous` it gives the paper's "$f^{-1}$ is linear and continuous" in full.

```coq
(* theories/cones/basic_lemmas.v
   Section variables: R : realType, P Q : coneType R,
   f : P -> Q linear, omega-continuous, injective, surjective ;
   invf : Q -> P the section provided by surjectivity. *)
Lemma invf_linear : is_linear invf.
```

### Lemma 2.11 (`linmap_bounded`, `linmap_norm`)

A linear map $f:P\to Q$ is bounded on the unit ball $\mathbf{B}P$, and the operator norm is $\lVert f\rVert=\sup_{x\in\mathbf{B}P}\lVert f(x)\rVert\in\mathbb{R}_{\geq 0}$. In Rocq, `linmap_bounded` produces a bound $M\geq 0$ dominating $\lVert f(x)\rVert$ on the ball; `linmap_norm` picks such an $M$ (via classical choice), with `linmap_norm_ge0` and `linmap_norm_ub` its defining properties.

> **Paper — Lemma 2.11** (arXiv 2212.02371, `content.tex:676`). If $f:P\to Q$ is linear then $f(\mathbf{B}P)$ is bounded. We set $\lVert f\rVert=\sup_{x\in\mathbf{B}P}\lVert f(x)\rVert\in\mathbb{R}_{\geq 0}$.

> **Difference.** The paper takes the *exact supremum* $\lVert f\rVert=\sup_{x\in\mathbf{B}P}\lVert f(x)\rVert$. The mechanisation records only that `linmap_norm` is *an* upper bound of $\{\lVert f(x)\rVert\mid x\in\mathbf{B}P\}$ (obtained by classical choice `cid` on `linmap_bounded`), not that it is the *least* upper bound — downstream cone-of-linear-maps clients (the precone $P\multimap Q$ in `cone_cat.v`) need only the bound to package their norm.

```coq
(* theories/cones/basic_lemmas.v — Section Lemma211,
   Variables R : realType, P Q : coneType R *)

Lemma linmap_bounded (f : P -> Q) :
  is_linear f ->
  exists M : R, 0 <= M /\
    forall x, cone_norm x <= 1 -> cone_norm (f x) <= M.

Definition linmap_norm (f : P -> Q) (Hf : is_linear f) : R :=
  projT1 (cid (linmap_bounded Hf)).

Lemma linmap_norm_ge0 (f : P -> Q) (Hf : is_linear f) :
  0 <= linmap_norm Hf.

Lemma linmap_norm_ub (f : P -> Q) (Hf : is_linear f) :
  forall x, cone_norm x <= 1 -> cone_norm (f x) <= linmap_norm Hf.
```

### Thm 2.18 (`cones_prod`, `cones_proj`, `cones_tuple`)

The category $\mathbf{Cones}$ has all small products. Given a family $(P_i)_{i\in I}$ of cones with no cardinality restriction on $I$, the product cone `cones_prod` consists of the bounded-norm families with componentwise operations and $\lVert\vec x\rVert=\sup_{i\in I}\lVert x_i\rVert$; `cones_proj` are the projections, `cones_tuple` the mediating tuple, with universal property `cones_tuple_proj` and uniqueness `cones_tuple_unique`.

> **Paper — Theorem 2.18** (arXiv 2212.02371, `content.tex:820`). The category $\mathbf{Cones}$ has all small products. Given a family $(P_i)_{i\in I}$ of cones (no cardinality restriction on $I$), their categorical product $(\mathop{\&}_{i\in I}P_i,(\mathsf{pr}_i)_{i\in I})$ is: $\mathop{\&}_{i\in I}P_i$ is the set of $\vec x=(x_i)_{i\in I}\in\prod_{i\in I}P_i$ with $(\lVert x_i\rVert)_{i\in I}$ bounded, componentwise operations, and $\lVert\vec x\rVert=\sup_{i\in I}\lVert x_i\rVert$; the projections are the set-theoretic projections; given $(f_i\in\mathbf{Cones}(Q,P_i))_{i\in I}$ the mediating morphism $\langle f_i\rangle_{i\in I}$ is characterised by $f(y)=(f_i(y))_{i\in I}$. In particular the terminal object ($I=\emptyset$) is $\top$.

> **Difference.** The paper's index $I$ is an arbitrary set; the Rocq family is indexed by an arbitrary `Type I`, matching "no cardinality restriction". The bounded-norm carrier is packaged as a record with a `cones_prod_bd` field carrying the boundedness witness, and the product norm is realised as the mathcomp-analysis `sup` of the componentwise norm set.

```coq
(* theories/cones/cone_cat.v — Section ProductsUniversal,
   Variables R : realType, I : Type, P : I -> coneType R,
             Q : coneType R, f : forall i, cones_hom Q (P i) *)

Definition cones_prod (R : realType) (I : Type) (P : I -> coneType R) :
  coneType R := cones_prod_car I P.

Definition cones_proj (i : I) : cones_hom (cones_prod P) (P i).

Definition cones_tuple : cones_hom Q (cones_prod P) :=
  ConesHom cones_tuple_fun
    cones_tuple_linear cones_tuple_continuous cones_tuple_norm_le1.

Lemma cones_tuple_proj (i : I) :
  cones_comp (cones_proj i) cones_tuple = f i.

Lemma cones_tuple_unique (h : cones_hom Q (cones_prod P)) :
  (forall i, cones_comp (cones_proj i) h = f i) -> h = cones_tuple.
```

The construction internals behind that Difference note have names. The carrier `cones_prod_car` is the $\Sigma$-type of a section $i\mapsto x_i$ together with the boundedness witness `cones_prod_bd`; pointwise addition and scaling preserve boundedness by (Normt) and (Normh). The norm is the mathcomp-analysis `sup` of the componentwise norm set `cones_prod_normset`, taken by Dedekind completeness and packaged as `cones_prod_norm`; (Normh)–(Normp) reduce componentwise, and the (Normc) witness `cones_prod_sup_ball` is the chain's componentwise supremum.

```coq
(* theories/cones/cone_cat.v — Section ConesProduct,
   Variables (R : realType) (I : Type) (P : I -> coneType R) *)
Record cones_prod_car : Type := MkConesProd {
  cones_prod_val : forall i : I, P i;
  cones_prod_bd  : exists M : R, forall i, cone_norm (cones_prod_val i) <= M;
}.

Definition cones_prod_normset (x : T) : set R :=
  [set y | exists i, y = cone_norm (cones_prod_val x i)].

Definition cones_prod_norm (x : T) : R := sup (cones_prod_normset x).

Definition cones_prod_sup_ball : T.
```

### Lemma 2.19 (`diagonal_collapse`)

Separate $\omega$-continuity of a two-argument map on $\omega$-closed subsets implies joint $\omega$-continuity. In the pointwise sup encoding, the load-bearing step is `diagonal_collapse`: a doubly-indexed, jointly monotone family collapses along the diagonal, so the row-sups are dominated by the diagonal sup.

> **Paper — Lemma 2.19** (arXiv 2212.02371, `content.tex:854`). Let $P$, $Q$, $R$ be cones, $A\subseteq P$ and $B\subseteq Q$ be $\omega$-closed (so $A\times B$ is $\omega$-closed in $P\mathbin{\&}Q$), and let $f:A\times B\to R$ be separately $\omega$-continuous. Then $f$ is $\omega$-continuous.

> **Difference.** The `is_omega_continuous` interface threads chain / unit-ball witnesses explicitly, so a fully-quantified two-argument statement would carry roughly a dozen proof-irrelevance hypotheses (documented at `cone_cat.v:846-880`). `diagonal_collapse` is the load-bearing pointwise form actually consumed downstream: given a jointly monotone doubly-indexed family $a$, the row-sup $\sup_k a(n,k)$ is $\leq$ the diagonal sup $\sup_k a(k,k)$. The double-sup expansion ($f(\sup u)(\sup v)=\sup_n\sup_k f(u_n)(v_k)$) then follows mechanically from separate continuity.

```coq
(* theories/cones/cone_cat.v — Section Lemma219,
   Variables R : realType, P Q S : coneType R *)

Lemma diagonal_collapse
  (a : nat -> nat -> S)
  (mono : forall n m k l,
      (n <= k)%N -> (m <= l)%N -> precone_le (a n m) (a k l))
  (diagch : forall n, precone_le (a n n) (a n.+1 n.+1))
  (diagub1 : forall n, cone_norm (a n n) <= 1)
  (rowch : forall n k, precone_le (a n k) (a n k.+1))
  (rowub1 : forall n k, cone_norm (a n k) <= 1) :
  forall n,
    precone_le (cone_sup_ball (fun k => a n k) (rowch n) (rowub1 n))
               (cone_sup_ball (fun k => a k k) diagch diagub1).
```

### Thm 2.20 (`cones_eq`, `cones_eq_incl`, `cones_eq_med`)

The category $\mathbf{Cones}$ has all binary equalisers and therefore is complete. The equaliser cone `cones_eq` of $f,g:P\to Q$ is the sub-cone $\{x\in P\mid f(x)=g(x)\}$; `cones_eq_incl` is the equalising inclusion (`cones_eq_incl_equ`), `cones_eq_med` the mediator (`cones_eq_med_factor`, `cones_eq_med_unique`), and `cones_eq_le_underlying` records that the inclusion reflects the order.

> **Paper — Theorem 2.20** (arXiv 2212.02371, `content.tex:884`). The category $\mathbf{Cones}$ has all binary equalisers and therefore is complete. Moreover, if $(E,e\in\mathbf{Cones}(E,P))$ is the equaliser of $f,g\in\mathbf{Cones}(P,Q)$ then $e$ reflects the order relation: if $x,y\in E$ satisfy $e(x)\leq_P e(y)$ then $x\leq_E y$.

> **Difference.** The paper reads "$\mathbf{Cones}$ is complete" as a corollary of having products (Thm 2.18) plus binary equalisers; the mechanisation provides exactly those data. The equaliser carrier `cones_eq_car` is a subtype record $\{$`cones_eq_val : P`; `cones_eq_eq : f(val) = g(val)`$\}$, with subtype extensionality supplied by `cones_eq_extensional`; the order-reflection direction ($e(x)\leq_P e(y)\Rightarrow x\leq_E y$) is `cones_eq_le_underlying`'s converse witnessed inside the same section.

```coq
(* theories/cones/cone_cat.v — Section EqualiserUniversal,
   Variables R : realType, P Q : coneType R,
             f g : cones_hom P Q, T : coneType R,
             h : cones_hom T P, Hh : cones_comp f h = cones_comp g h *)

Definition cones_eq (R : realType) (P Q : coneType R)
  (f g : cones_hom P Q) : coneType R := cones_eq_car f g.

Definition cones_eq_incl : cones_hom (cones_eq f g) P.

Lemma cones_eq_incl_equ :
  cones_comp f cones_eq_incl = cones_comp g cones_eq_incl.

Definition cones_eq_med : cones_hom T (cones_eq f g).

Lemma cones_eq_med_factor : cones_comp cones_eq_incl cones_eq_med = h.

Lemma cones_eq_med_unique (h' : cones_hom T (cones_eq f g)) :
  cones_comp cones_eq_incl h' = h -> h' = cones_eq_med.

Lemma cones_eq_le_underlying (x y : cones_eq f g) :
  precone_le x y -> precone_le (cones_eq_val x) (cones_eq_val y).
```

### Lemma 2.21 / Prop 2.22 (`cones_iso_preserves_norm`)

An isomorphism in $\mathbf{Cones}$ preserves the norm exactly. The paper proves this in two steps — Lemma 2.21 bounds $\lVert f^{-1}\rVert$ below and Proposition 2.22 concludes $\lVert f\rVert=1$; the constructive mechanisation states the endpoint directly as pointwise norm preservation.

> **Paper — Lemma 2.21** (arXiv 2212.02371, `content.tex:959`). Let $P,Q$ be cones with $P\neq 0$ and $f:P\to Q$ linear, continuous and bijective. Then $\lVert f\rVert\neq 0$ and $\lVert f^{-1}\rVert\geq \lVert f\rVert^{-1}$.

> **Paper — Proposition 2.22** (arXiv 2212.02371, `content.tex:985`). If $f\in\mathbf{Cones}(P,Q)$ is an iso and $P\neq 0$, then $\lVert f\rVert=1$.

> **Difference.** Because the operator-norm value $\lVert f\rVert$ is not materialised in the `cones_hom_norm_le1` encoding (it is only introduced as *a* bound in Lemma 2.11), the paper's chain 2.21 $\to$ 2.22 is restated as exact pointwise norm preservation for a two-sided-invertible morphism: if $f$ has an inverse $g$ in $\mathbf{Cones}$ (with $g\circ f=\mathrm{id}$ and $f\circ g=\mathrm{id}$) then $\lVert f(x)\rVert=\lVert x\rVert$ for all $x$. This is the constructively usable content of $\lVert f\rVert=1$ (see `cone_cat.v:1355-1361`); it drops the $P\neq 0$ hypothesis, which is needed only to name the numeric value.

```coq
(* theories/cones/cone_cat.v — Section ConesIso,
   Variables R : realType, P Q : coneType R *)

Lemma cones_iso_preserves_norm
  (f : cones_hom P Q) (g : cones_hom Q P)
  (Hgf : cones_comp g f = cones_id P)
  (Hfg : cones_comp f g = cones_id Q) :
  forall x : P, cone_norm (cones_hom_fun f x) = cone_norm x.
```

### Lemma 2.23 (`transport_isPrecone`)

Given a cone $P$ and a bijection $f:P\to S$ onto a set $S$, there is exactly one cone structure on $S$ making $f$ an iso in $\mathbf{Cones}$. The transported operations are $s+t:=f(f^{-1}s+f^{-1}t)$, $r\cdot s:=f(r\cdot f^{-1}s)$, $\lVert s\rVert:=\lVert f^{-1}s\rVert$; `transport_isPrecone` assembles the transported *precone* structure from the `trans_*` axiom lemmas.

> **Paper — Lemma 2.23** (arXiv 2212.02371, `content.tex:1003`). Let $P$ be a cone, $S$ a set and $f:P\to S$ a bijective function. There is exactly one cone structure on $S$ for which $f$ becomes an iso in $\mathbf{Cones}$.

> **Difference.** The mechanisation establishes *existence* of the transported **precone** structure only — `transport_isPrecone : isPrecone R S`, built from `trans_add`/`trans_scale`/`trans_norm` and the twelve `trans_*` axiom lemmas. Packaging the full `HB.instance` of the cone (with the norm axioms) is deferred as a downstream task and re-stated per target file when needed concretely (see the note at `cone_cat.v:1465-1470`); uniqueness is exactly the observation that every transported axiom is determined by $f$.

```coq
(* theories/cones/cone_cat.v — Section ConesTransport,
   Variables R : realType, P : coneType R, S : Type,
             f : P -> S, finv : S -> P,
             finvK : forall s, f (finv s) = s,
             fK : forall x, finv (f x) = x *)

Definition trans_add (s t : S) : S := f (precone_add (finv s) (finv t)).
Definition trans_scale (r : {nonneg R}) (s : S) : S :=
  f (precone_scale r (finv s)).
Definition trans_norm (s : S) : R := cone_norm (finv s).

Definition transport_isPrecone : isPrecone R S :=
  isPrecone.Build R S
    trans_addA trans_addC trans_add0
    trans_scale_DAr trans_scale_DAl trans_scale_A
    trans_scale_1 trans_scale_0r trans_scale_0l
    trans_cancel trans_pos.
```

### §2.3 ⊤ / ⊥ (`ConeBot.T`, `ConeOne.T`)

The two smallest cones, and the only concrete ones the paper needs before §3. $\top$ is the *zero-dimensional* cone: one element, all operations constant, norm $\equiv 0$, every $\omega$-sup the unique inhabitant; it is the terminal object of $\mathbf{Cones}$ (the $I=\emptyset$ case of Thm 2.18). $\bot = \mathbf{1}$ is the *one-dimensional* cone $\mathbb{R}_{\geq 0}$ with the ring addition and multiplication as cone addition and scalar action, and $\lVert r\rVert = r$; it is the codomain of every test (a test at arity $X$ is pointwise a morphism $C\multimap\bot$) and the target of the dual $P' = (P\multimap\bot)$ of Def 2.14, so essentially all of §3 is stated relative to it.

> **Paper — §2.3 "Basic properties"** (arXiv 2212.02371 / LMCS 21(1:1), p. 13). Using the notations of LL for the multiplicative constants, there is a cone $\mathbf{1}=\bot$ whose set of elements is $\mathbb{R}_{\geq 0}$ and $\lVert x\rVert = x$: the 1-dimensional cone. And using the notations of LL for the additive constants, there is also a cone $\mathbf{0}=\top$ whose only element is $0$: the 0-dimensional cone.

> **Difference — the `Module` wrappers, and the LL-transposed names.** Each example lives in its own `Module`, and the two names read backwards unless one keeps the LL dictionary in mind: `ConeBot.T` carries $\top$ (the *zero-dimensional* cone) and `ConeOne.T` carries $\mathbf{1}=\bot$, so grepping for "bot" finds the wrong module. The carriers are asymmetric. $\top$ needs a **fresh** carrier and gets one — `Inductive T : Type := zero_top`, a one-constructor type declared for this purpose — because HB attaches at most one canonical `isPrecone` / `isCone` instance per carrier type, and reusing `unit` (or any type the library already uses) would either clash with another instance or silently make some other structure canonical. $\bot$ needs none: `ConeOne.T` is a `Local Notation` for mathcomp's `{nonneg R}`, so the cone structure is installed **on `{nonneg R}` itself** — which is the point, since that is the type the norm and every test lands in. What the `Module` wrapper buys there is name hygiene: both modules declare `add`, `scale`, `norm` and `sup_ball`, so without it the second set would shadow the first (as it is, an unqualified `norm` in `examples_cone.v` is `ConeBot.norm`). Because `ConeOne.T` is a notation rather than a definition, its operations are reachable only as `ConeOne.add` / `ConeOne.norm`; the rewriting equations `precone_add_E` and `precone_leE`, which identify the abstract cone operations with the underlying `{nonneg R}` arithmetic and order, are what downstream proofs actually compute with.

```coq
(* theories/cones/examples_cone.v — Module ConeBot, Variable R : realType:
   the zero-dimensional cone ⊤ *)
Inductive T : Type := zero_top : T.

Lemma all_zero (x : T) : x = zero_top.

Definition norm (_ : T) : R := 0.

(* Module ConeOne, Variable R : realType: the one-dimensional cone ⊥ = 1.
   Its carrier is [Local Notation T := {nonneg R}], its norm [x%:num], and
   its precone operations are the {nonneg R} ring operations: *)
Lemma precone_add_E (x y : T) : precone_add x y = add x y.

Lemma precone_leE (x y : T) : precone_le x y <-> x%:num <= y%:num.
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
| Def 3.15 | The rescaled measurable cone $\alpha B$ ($\alpha>0$): same carrier as $B$, norm $\lVert x\rVert_{\underline{\alpha B}}=\alpha^{-1}\lVert x\rVert_{\underline{B}}$. | `alpha_rescale_car`, `αB_norm`, `isMCone` instance — `theories/mcones/mcone_cat.v` |
| Prop 3.11 | Dual norm separation: $\lVert x\rVert = \sup_{x' \in \mathcal{B}(\underline{B}')} \langle x, x'\rangle$, with the supremum attained as an adherent point. | `mcone_norm_le_pairing_ub`, `mcone_test_pairing_adherent` — `theories/mcones/mcone_cat.v` (`Section Proposition311`) |
| Def 3.16 (§3.4.1) | The *measure cone* $\mathsf{FMeas}(X)$ of finite measures on $X$, with tests $\widetilde{U} : \mu \mapsto \mu(U)$ for $U \in \sigma_X$. | `fmeas`, the `FMeas` HB instance — `theories/mcones/fmeas.v` |
| Lem 3.17 | Measure push-forward $\phi_*$ is an $\mathbf{MCones}$-morphism, and $\mathsf{FMeas} : \mathbf{Ar}\to\mathbf{MCones}$ is functorial. | `fmeas_push`, `fmeas_push_id`, `fmeas_push_comp` — `theories/mcones/fmeas.v` |
| Def 3.7 | A *path* of arity $X$ is a bounded map $\gamma : X \to \underline{C}$ whose pointwise test pairings are jointly measurable. | `path_car` — `theories/mcones/path.v`; `path_int_exists` lives in `theories/icones/examples_icone.v` (see § 4 below) |
| §3.2.2 Path cone | The set $\mathsf{Path}(X,B)$ of measurable paths $X\to B$ is itself a *cone*: pointwise algebra, sup-norm $\lVert\gamma\rVert=\sup_{r\in X}\lVert\gamma(r)\rVert$, and a (Normc) witness computed pointwise from $B$'s, whose test-measurability is a monotone-convergence step. | `path_norm`, `path_sup_ball`, `path_sup_ball_meas`, the `isCone` instance — `theories/mcones/path.v` |
| §3.2.2 Path tests | The test family $\varphi\rhd m$ with $(\varphi\rhd m)(s,\gamma)=m(s,\gamma(\varphi(s)))$, and the measurability structure $\mathcal{M}_Y=\{\varphi\rhd m\}$ it generates on $\mathsf{Path}(X,B)$. | `path_test`, `path_mcone_M`, `path_mcone_M_comp`, `path_mcone_M_sep`, `path_mcone_M_norm`, the `isMCone` instance — `theories/mcones/path.v` |
| Lem 3.9 | The constant function $\gamma = \boldsymbol\lambda r\in X\cdot x$ is a measurable path. | `const_path_measurable` — `theories/mcones/mcone.v` |
| Lem 3.10 | If $\gamma : X\to\underline{C}$ is a measurable path and $\phi\in\mathbf{Ar}(Y,X)$, then $\gamma\mathrel{\circ}\phi$ is a measurable path. | `reindex_path_measurable` — `theories/mcones/mcone.v` |
| Lem 3.19 | The path-flattening iso $\mathrm{fl}_{X,Y}(\eta)=\boldsymbol\lambda(r,s)\cdot\eta(r)(s)$ and its inverse (bivariate-function level). | `path_fl_fun`, `path_fl_inv_fun`, `path_fl_fun_inv` — `theories/mcones/path.v` |
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

> **Difference — the product is only *propositionally* the product measurable space, and its universal property is what repairs that.** `MeasSubcat` keeps `ar_prod X Y` abstract and records `ar_prod_carrier_eq : ar_carrier (ar_prod X Y) = (ar_carrier X * ar_carrier Y)%type` as a propositional equality rather than making the carrier *definitionally* a product. *Why:* `Ar` is an abstract `Record` parametrising the whole §3+ tower, so it cannot dictate how an instance realises its products; the two measurability fields `ar_prod_uncast_meas` / `ar_prod_cast_meas` pay the transport cost once, at the abstraction boundary (in any standard realisation the equality is `eq_refl` and both fields are `measurable_id`). What makes the encoding usable downstream is the universal property: `ar_prod_fst` / `ar_prod_snd` are the transported projections, `ar_pair f g` is the pairing, and `ar_pair_fst` / `ar_pair_snd` / `ar_pair_uniqueE` say that it is the *unique* $\mathbf{Ar}$-morphism through which $f$ and $g$ factor — uniqueness reducing exactly to the cast/uncast round-trips `ar_prod_castK` and `ar_prod_uncastK`. This is the property Lem 3.19 (path flattening) and the bivariate test-reindexing arguments consume.

```coq
(* theories/mcones/ar.v — Section ArProdHelpers,
   Variables (R : realType) (Ar : MeasSubcat R) (X Y : ar_obj Ar) *)
Definition ar_prod_uncast (p : ar_carrier Ar (ar_prod Ar X Y)) :
    (ar_carrier Ar X * ar_carrier Ar Y)%type :=
  eq_rect _ (fun T : Type => T) p _ (ar_prod_carrier_eq Ar X Y).

Definition ar_prod_cast (p : (ar_carrier Ar X * ar_carrier Ar Y)%type) :
    ar_carrier Ar (ar_prod Ar X Y) :=
  eq_rect_r (fun T : Type => T) p (ar_prod_carrier_eq Ar X Y).

Lemma ar_prod_castK p : ar_prod_uncast (ar_prod_cast p) = p.

Lemma ar_prod_uncastK x : ar_prod_cast (ar_prod_uncast x) = x.

Definition ar_prod_fst : ar_hom Ar (ar_prod Ar X Y) X := ar_prod_fst_fun.

Definition ar_prod_snd : ar_hom Ar (ar_prod Ar X Y) Y := ar_prod_snd_fun.

(* Section ArPair, Variables (Z : ar_obj Ar) (f : ar_hom Ar Z X)
   (g : ar_hom Ar Z Y) *)
Definition ar_pair : ar_hom Ar Z (ar_prod Ar X Y) := ar_pair_fun.

Lemma ar_pair_fst z : ar_prod_fst (ar_pair z) = f z.

Lemma ar_pair_snd z : ar_prod_snd (ar_pair z) = g z.

Lemma ar_pair_uniqueE (Z : ar_obj Ar)
    (h : ar_hom Ar Z (ar_prod Ar X Y)) (z : ar_carrier Ar Z) :
  ar_prod_cast (ar_prod_fst (h z), ar_prod_snd (h z)) = h z.
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

The Difference note above says that (Msmeas) "is carried by the `test_of` type of tests, not spelled as a separate mixin field". Here is what that type *is*. A `test_of Ar X C` bundles a function $m : X\to C\to\mathbb{R}$ with eight obligations: `test_meas` — (Msmeas) proper, the partial application $r\mapsto m\,r\,x$ is measurable for every $x$ in the unit ball; `test_ge0` and `test_le1` — the paper's "lands in $[0,1]$" condition, split into non-negativity everywhere and the bound $m\,r\,x\le 1$ on the ball; `test_lin0`, `test_linD`, `test_linZ` — linearity in the cone argument; `test_cont` — $\omega$-continuity in the cone argument, stated in the sufficient least-upper-bound form "below every upper bound $N$ of $(m\,r\,u_n)$"; and `test_norm_le` — the operator-norm bound $m\,r\,x\le\lVert x\rVert$, which together with the linearity fields says that $\lambda x\,.\,m\,r\,x$ is a $\mathbf{Cones}$-morphism $C\multimap\bot$, i.e. an element of the dual $C'$ as the paper requires. Two tests are equal as soon as their functions agree pointwise (`test_eq`, by `Prop`-irrelevance), and `test_reindex φ m` is the reindexed test $(s,x)\mapsto m\,(\varphi\,s)\,x$ that (Mscomp) is stated about — all eight obligations transport along $\varphi$ because $\varphi$ is itself measurable.

> **Difference — `test_of` is a bundled record, not a subset of $(C')^X$.** The paper writes $\mathcal{M}_X\subseteq(C')^X$ and reads measurability off the ambient function space. The mechanisation makes a test a `Record` bundling its function with all of its proofs — the cone-side counterpart of mathcomp-analysis's `{mfun _ >-> _}`, but with codomain `R` rather than a general `measurableType` — so `mcone_M X : set (test_of Ar X C)` is a set of *bundled* tests. `test_eq` is what restores the paper's extensional reading of that set.

```coq
(* theories/mcones/mcone.v — Section TestOf,
   Variables (R : realType) (Ar : MeasSubcat R) (X : ar_obj Ar) (C : coneType R) *)
Record test_of : Type := MkTestOf {
  test_fun     :> ar_carrier Ar X -> C -> R;
  test_meas    : _;
  test_ge0     : _;
  test_le1     : _;
  test_lin0    : _;
  test_linD    : _;
  test_linZ    : _;
  test_cont    : _;
  test_norm_le : _;
}.

Lemma test_eq (m1 m2 : test_of Ar X C) :
  (forall r x, test_fun m1 r x = test_fun m2 r x) -> m1 = m2.

(* Section TestReindex, Variables (Y : ar_obj Ar) (φ : ar_hom Ar Y X)
   (m : test_of Ar X C) *)
Definition test_reindex_fun : ar_carrier Ar Y -> C -> R :=
  fun s x => test_fun m (φ s) x.

Definition test_reindex : test_of Ar Y C.
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

As in $\mathbf{Cones}$, the category laws of $\mathbf{MCones}$ are proved rather than assumed: `mcones_hom_eq` is subtype extensionality on the pair (underlying `cones_hom`, path-preservation proof), and `mcones_compIl` / `mcones_compIr` / `mcones_compA` follow from it, with `mcones_id` the identity morphism (the identity `cones_hom` paired with the trivial path-preservation witness).

```coq
(* theories/mcones/mcone_cat.v — Section MConesCat,
   Variables (R : realType) (Ar : MeasSubcat R) *)
Lemma mcones_hom_eq (f g : mcones_hom Ar B C) :
  (forall x, cones_hom_fun (mcones_hom_cones f) x =
             cones_hom_fun (mcones_hom_cones g) x) -> f = g.

Definition mcones_id : mcones_hom Ar B B :=
  MkMConesHom (cones_id B) mcones_id_pres_path.

Lemma mcones_compIl (B C : MCone.type Ar) (f : mcones_hom Ar B C) :
  mcones_comp (mcones_id Ar C) f = f.

Lemma mcones_compIr (B C : MCone.type Ar) (f : mcones_hom Ar B C) :
  mcones_comp f (mcones_id Ar B) = f.

Lemma mcones_compA (B1 B2 B3 B4 : MCone.type Ar)
  (h : mcones_hom Ar B3 B4)
  (g : mcones_hom Ar B2 B3)
  (f : mcones_hom Ar B1 B2) :
  mcones_comp h (mcones_comp g f) = mcones_comp (mcones_comp h g) f.
```

> **Where the "equivalently" clause is used.** The test-side reading quoted above is packaged as reusable lemmas in `theories/icones/test_pullback.v` — `test_pullback_meas`, its bivariate form `test_pullback_meas_bivar` (the path argument folded out of a pair through `ar_prod`), and the continuity companion `test_pullback_cont` — and is what paper § 5.3 consumes to lift the internal-hom action $h\multimap g$ to an $\mathbf{ICones}$ morphism (Prop 5.8). Only the forward direction (path preservation $\Rightarrow$ test measurability) is formalised; see *§ 5.3 test-pullback* in § 5.

### Def 3.15 (`alpha_rescale_car`)

For a measurable cone $B$ and a scalar $\alpha>0$, the *rescaled* measurable cone $\alpha B$ has the same carrier and precone operations as $B$, but its norm is $\lVert x\rVert_{\underline{\alpha B}}=\alpha^{-1}\lVert x\rVert_{\underline{B}}$; the test family is obtained by scaling every test of $B$ by $\alpha^{-1}$. The `alpha_rescale_car` record is a thin wrapper giving $\alpha B$ a distinct carrier identity for HB inference, over which a full `isMCone` instance is installed.

> **Paper — Definition 3.15** (arXiv 2212.02371, `def:mes-cone-homothetie`). Let $B$ be a measurable cone and $\alpha\in\mathbb{R}$ with $\alpha>0$. Then $\alpha B$ is the measurable cone which is defined exactly as $B$ apart for the norm which is given by $\lVert x\rVert_{\underline{\alpha B}}=\alpha^{-1}\lVert x\rVert_{\underline{B}}$. (Notice $\mathcal{B}(\underline{\alpha B})=\alpha\,\mathcal{B}(\underline{B})=\{x\in\underline{B}\mid\lVert x\rVert_{\underline{B}}\le\alpha\}$.)

```coq
(* theories/mcones/mcone_cat.v — Section AlphaRescaleDef,
   Variables (R : realType) (Ar : MeasSubcat R) (α : pos_real R) (B : MCone.type Ar) *)
Record alpha_rescale_car (α : pos_real) (B : MCone.type Ar) : Type :=
  MkAlphaRescale { alpha_rescale_val : B }.

Definition αB_norm (x : alpha_rescale_car α B) : R :=
  (α : R)^-1 * cone_norm (alpha_rescale_val x).

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (α : pos_real R) (B : MCone.type Ar) :=
  @isMCone.Build R Ar (alpha_rescale_car α B)
    (@αB_mcone_M R Ar α B)
    (@αB_mcone_M_comp R Ar α B)
    (@αB_mcone_M_sep R Ar α B)
    (@αB_mcone_M_norm R Ar α B).
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

> **Paper — Remark 3.12** (arXiv 2212.02371 / LMCS 21(1:1), p. 19). One main purpose of the condition (Msnorm) is to get the above highly desirable property. We could have expected to get (Mssep) and (Msnorm) for free by means of a Hahn Banach theorem for cones as in [Sel04]. However, the counter-example of Remark 2.16, suggested to us by one of the reviewers of this paper, shows that such a separation property does not hold in our setting. The very nice Hahn Banach theorem proven in [Sel04] relies on the assumption that cones are continuous domains, an assumption that we cannot afford here because we need our cones to define a complete category in order to apply the special adjoint functor theorem which is our main tool for equipping $\mathbf{ICones}$ with a tensor product and with an exponential. Fortunately, we can take this Hahn Banach separation property as one of our axioms on the measurability tests, and proving that this property is preserved by all limits does not induce noticeable technical difficulties.

> **Why (Msnorm) is an axiom.** Remark 3.12 is the reason `mcone_M_norm` is a *field* of the `isMCone` mixin rather than a derived lemma: there is no Hahn–Banach theorem for cones (paper Remark 2.16 exhibits a non-trivial cone whose dual is $\{0\}$), so the separation property cannot be recovered from the cone structure and must be assumed of the tests. The pay-off is that it is then an obligation every construction of §4–§6 must discharge — and does: each limit, internal hom, tensor and exponential in this development carries its own `*_mcone_M_norm` proof, which is why the axiom "survives all the limit constructions".

> **Direction split.** The $\geq$ half of Prop 3.11 is not an extra argument at all: it is the `test_norm_le` field of every test, read at arity $0$, packaged as `mcone_test_pairing_ub` — every pairing $\langle x,x'\rangle$ is bounded by $\lVert x\rVert$, i.e. $\lVert x\rVert$ is an upper bound of `mcone_test_pairing_set x`. The $\le$ half is the (Msnorm) invocation `mcone_test_pairing_adherent` above.

```coq
(* theories/mcones/mcone_cat.v — Section Proposition311,
   Variables (R : realType) (Ar : MeasSubcat R) (B : MCone.type Ar) *)
Definition mcone_test_pairing_set (x : B) : set R :=
  [set y | exists2 m : test_of Ar (ar_zero Ar) B,
             mcone_M (ar_zero Ar) m & y = test_fun m (ar_zero_pt Ar) x].

Lemma mcone_test_pairing_ub (x : B) :
  ubound (mcone_test_pairing_set x) (cone_norm x).
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

> **Difference — why the carrier is a wrapper, and what the wrapper buys.** `fmeas R X` is not mathcomp-analysis's `{measure set X -> \bar R}` itself but a record wrapping one, with two structural invariants: `fmeas_fin` (every measurable set has finite measure, so the norm $\lVert\mu\rVert=\mu(X)$ is a real) and `fmeas_canonical` (the *canonicality* invariant: $\mu(U)=0$ for every non-measurable $U$). The second is the load-bearing one. Without it, two measures agreeing on the whole $\sigma$-algebra could still differ off it, and equality of cone elements would have to be a setoid relation carried through every axiom proof. With it, `fmeas_eq` reduces equality of `fmeas` elements to agreement on measurable sets — which is exactly the paper's notion — so every cone-axiom proof on $\mathsf{FMeas}(X)$ is a plain Leibniz-equality argument and (Mssep) is literally "two finite measures agreeing on every measurable set are equal".

```coq
(* theories/mcones/fmeas.v — Variables R X *)
Lemma fmeas_eq (m1 m2 : fmeas) :
  (forall U, measurable U -> fmeas_mu m1 U = fmeas_mu m2 U) -> m1 = m2.
```

### Lem 3.17 (`fmeas_push`)

Push-forward of measures along $\phi\in\mathbf{Ar}(X,Y)$ is a $\mathbf{Cones}$-morphism $\mathsf{FMeas}(X)\to\mathsf{FMeas}(Y)$, and the operation $\mathsf{FMeas}$ extends to a functor $\mathbf{Ar}\to\mathbf{MCones}$ acting on morphisms by push-forward, $\mathsf{FMeas}(\phi)=\phi_*$. The packaged morphism is `fmeas_push`; functoriality is witnessed by `fmeas_push_id` and `fmeas_push_comp`.

> **Paper — Lemma 3.17** (arXiv 2212.02371, `lemma:pushf-measurable`). We have $\phi_*\in\mathbf{MCones}(\mathsf{FMeas}(X),\mathsf{FMeas}(Y))$. The operation $\mathsf{FMeas}$ on measurable cones extends to a functor $\mathsf{FMeas}:\mathbf{Ar}\to\mathbf{MCones}$, acting on morphisms by measure push-forward: $\mathsf{FMeas}(\phi)=\phi_*$.

> **Difference.** The mechanisation packages $\phi_*$ as a `cones_hom` (a linear, $\omega$-continuous map of norm $\le 1$) rather than as a full `mcones_hom` record: path-preservation is not bundled at this point. The packaged mcones/icones-morphism version, `FMeas_fmap`, lives later in `theories/exp/coalgebra.v` for the ICones/coalgebra layer. Functoriality is stated on the underlying functions ($=1$) — `fmeas_push_id` and `fmeas_push_comp` — rather than as categorical equalities.

```coq
(* theories/mcones/fmeas.v — Section FMeasPushforward,
   Variables (R : realType) (Ar : MeasSubcat R) (X Y : ar_obj Ar) (φ : ar_hom Ar X Y) *)
Definition fmeas_push :
  cones_hom (fmeas R (ar_carrier Ar X)) (fmeas R (ar_carrier Ar Y)) :=
  ConesHom fmeas_push_fun fmeas_push_is_linear fmeas_push_omega_continuous
           fmeas_push_norm_le.

Lemma fmeas_push_id (X : ar_obj Ar) (φid : ar_hom Ar X X) :
  φid =1 idfun ->
  cones_hom_fun (fmeas_push φid) =1 @idfun (fmeas R (ar_carrier Ar X)).

Lemma fmeas_push_comp (X Y Z : ar_obj Ar)
    (f : ar_hom Ar X Y) (g : ar_hom Ar Y Z) (gf : ar_hom Ar X Z) :
  gf =1 g \o f ->
  cones_hom_fun (fmeas_push gf) =1
  (cones_hom_fun (fmeas_push g)) \o (cones_hom_fun (fmeas_push f)).
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

`path_eq` is the extensionality principle that makes the wrapper usable: two paths are equal as soon as their underlying functions agree pointwise, the `is_measurable_path` proof field being discarded by `Prop`-irrelevance. Every algebraic law of the path cone below (`path_addA`, `path_addC`, `path_scale_A`, …) is proved by `apply: path_eq => r` followed by the corresponding law in $B$.

```coq
(* theories/mcones/path.v — Section PathCarrier,
   Variables (R : realType) (Ar : MeasSubcat R) (X : ar_obj Ar)
             (B : MCone.type Ar) *)
Lemma path_eq (γ1 γ2 : path_car) :
  (forall r, path_fun γ1 r = path_fun γ2 r) -> γ1 = γ2.
```

### §3.2.2 Path cone (`path_norm`, `path_sup_ball`, `path_sup_ball_meas`)

The set of measurable paths $X\to B$ is not merely a set: it carries the *pointwise* precone structure inherited from $B$ (so $(\gamma_1+\gamma_2)(r)=\gamma_1(r)+\gamma_2(r)$ and $(\lambda\gamma)(r)=\lambda\cdot\gamma(r)$, with `path_addA`, `path_addC`, `path_scale_A` and their siblings all proved by `path_eq` plus the corresponding law in $B$), the sup-norm $\lVert\gamma\rVert=\sup_{r\in X}\lVert\gamma(r)\rVert$ — well defined because a path is by definition bounded — and the cone order $\gamma_1\le\gamma_2\iff\forall r\,.\,\gamma_1(r)\le\gamma_2(r)$ (`path_le_pointwise`). The only non-obvious axiom is (Normc), and it is where the *measurable*-path condition has to be re-established: the candidate least upper bound is built pointwise from $B$'s own `cone_sup_ball` (`path_sup_ball_fun`), and one must show that this pointwise sup is again a measurable path. That is `path_sup_ball_meas`, the monotone-convergence step — for each test $m\in\mathcal{M}^B_Y$ the family $(s,r)\mapsto m(s,\gamma_n(r))$ is an increasing sequence of measurable functions $Y\times X\to[0,1]$ whose pointwise limit is $(s,r)\mapsto m(s,\gamma(r))$, so the limit is measurable. The packaged witness is `path_sup_ball`, with `path_sup_ball_ub` / `path_sup_ball_lub` / `path_sup_ball_norm` its three (Normc) obligations, and the `isCone` instance closes the cone layer of $\mathsf{Path}(X,B)$.

> **Paper — §3.2.2 "The measurable cone of paths"** (arXiv 2212.02371 / LMCS 21(1:1), p. 21). Let $C$ be an object of $\mathbf{MCones}$ and $X\in\mathbf{Ar}$. Let $P$ be the set of all measurable paths $\gamma:X\to C$. We turn $P$ into a precone by defining the algebraic laws in the obvious pointwise manner. […] Then we have $\gamma_1\leq\gamma_2$ iff $\forall r\in X\ \gamma_1(r)\leq\gamma_2(r)$ […]. Given $\gamma\in P$ we set $$\lVert\gamma\rVert=\sup_{r\in X}\lVert\gamma(r)\rVert$$ which is well defined by our assumption that $\gamma$ is bounded. This satisfies all the required conditions for turning $P$ into a cone, the only non obvious one being (Normc). So let $(\gamma_n)_{n\in\mathbb{N}}$ be an increasing sequence of elements of $P$ such that $\forall n\in\mathbb{N}\ \forall r\in X\ \lVert\gamma_n(r)\rVert\leq 1$. We define $\gamma:X\to P$ by $\gamma(r)=\sup_{n\in\mathbb{N}}\gamma_n(r)\in\mathbf{B}C$ which is well defined since for each $r\in X$ the sequence $(\gamma_n(r))_{n\in\mathbb{N}}$ is increasing in $\mathbf{B}C$. It suffices to check that $\gamma$ satisfies the measurability condition, so let $Y\in\mathbf{Ar}$ and $m\in\mathcal{M}^C_Y$, we have by $\omega$-continuity of $m$ in its second argument $$\lambda(s,r)\in Y\times X\cdot m(s,\gamma(r))=\lambda(s,r)\in Y\times X\cdot\sup_{n\in\mathbb{N}}m(s,\gamma_n(r))$$ which is measurable by the monotone convergence theorem of measure theory (observing that $(\lambda(s,r)\in Y\times X\cdot m(s,\gamma_n(r)))_{n\in\mathbb{N}}$ is an increasing sequence of measurable functions $Y\times X\to[0,1]$).

> **Paper — Remark 3.18** (arXiv 2212.02371 / LMCS 21(1:1), p. 21). Remember that it is precisely for being able to prove this kind of properties that we assume the unit balls of cones to be complete only for increasing chains and not for arbitrary directed sets.

> **Difference — how the monotone-convergence step is discharged.** The paper appeals to "the monotone convergence theorem of measure theory". `path_sup_ball_meas` uses the *pointwise-limit* form rather than the integral form (mathcomp-analysis's `monotone_convergence` is about integrals): the real sequence $n\mapsto m(s,\gamma_n(r))$ is shown nondecreasing (from `path_le_pointwise` plus `test_linD` / `test_ge0`) and bounded by $1$ (from `test_le1`), so `nondecreasing_cvgn` gives convergence to its supremum; `test_cont` and `cone_sup_ball_ub` identify that supremum with $m(s,(\sup_n\gamma_n)(r))$ by antisymmetry, and `measurable_fun_cvg` concludes. The norm is likewise a concrete operator: `path_norm` is the mathcomp-analysis `sup` of `path_normset`, whose `has_sup` obligation is discharged by the boundedness field of `is_measurable_path` (`path_normset_has_ubound`) and by non-emptiness of every $\mathbf{Ar}$-object (`ar_point`, used in `path_normset_nonempty`) — the one place §3's "all objects of $\mathbf{Ar}$ are non-empty" assumption is consumed in this file.

```coq
(* theories/mcones/path.v — Sections PathAlgebra, PathNorm, PathSupBall,
   Variables (R : realType) (Ar : MeasSubcat R) (X : ar_obj Ar)
             (B : MCone.type Ar) *)
Lemma path_addA : associative path_add.

Lemma path_addC : commutative path_add.

Lemma path_scale_A (r s : {nonneg R}) γ :
  path_scale (r%:num * s%:num)%:nng γ =
  path_scale r (path_scale s γ).

Definition path_normset γ : set R :=
  [set y | exists r : ar_carrier Ar X, y = cone_norm (path_fun γ r)].

Definition path_norm γ : R := sup (path_normset γ).

Lemma path_norm_ub γ r : cone_norm (path_fun γ r) <= path_norm γ.

Lemma path_le_pointwise γ1 γ2 :
  precone_le γ1 γ2 -> forall r, precone_le (path_fun γ1 r) (path_fun γ2 r).

(* (Normc): the candidate lub, built pointwise from B's own sup_ball. *)
Definition path_sup_ball_fun
  (u : nat -> path_car Ar X B)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, path_norm (u n) <= 1)
  (r : ar_carrier Ar X) : B :=
  cone_sup_ball (fun n => path_fun (u n) r)
                (path_sup_ball_chain_pw uch r)
                (path_sup_ball_ub1_pw ub1 r).

(* The monotone-convergence step: the pointwise sup is again a path. *)
Lemma path_sup_ball_meas
  (u : nat -> path_car Ar X B)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, path_norm (u n) <= 1)
  (Y : ar_obj Ar) (m : test_of Ar Y B) :
  mcone_M Y m ->
  measurable_fun
    [set: (ar_carrier Ar Y * ar_carrier Ar X)%type]
    (fun p : (ar_carrier Ar Y * ar_carrier Ar X)%type =>
       test_fun m p.1 (path_sup_ball_fun uch ub1 p.2) : R).

Definition path_sup_ball
  (u : nat -> path_car Ar X B)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, path_norm (u n) <= 1) : path_car Ar X B :=
  MkPath (path_sup_ball_is_path uch ub1).

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (X : ar_obj Ar) (B : MCone.type Ar) :=
  @isCone.Build R (path_car Ar X B)
    (@path_norm R Ar X B)
    (@path_normh R Ar X B) (@path_normz R Ar X B)
    (@path_normt R Ar X B) (@path_normp R Ar X B)
    (@path_sup_ball R Ar X B)
    (@path_sup_ball_ub R Ar X B)
    (@path_sup_ball_lub R Ar X B)
    (@path_sup_ball_norm R Ar X B).
```

### §3.2.2 Path tests (`path_test`, `path_mcone_M`, `path_mcone_M_comp`, `path_mcone_M_sep`, `path_mcone_M_norm`)

This is the construction that first justifies giving tests a *parameter* in $\mathbf{Ar}$ at all. Given $Y\in\mathbf{Ar}$, a reindexing map $\varphi\in\mathbf{Ar}(Y,X)$ and a test $m\in\mathcal{M}^B_Y$, the test $\varphi\rhd m$ on $\mathsf{Path}(X,B)$ is $(\varphi\rhd m)(s,\gamma)=m(s,\gamma(\varphi(s)))$ — the arity parameter $s$ is used *twice*, once as the test's own parameter and once as the point at which the path is sampled, which is impossible for a parameterless test. In Rocq that function is `path_test_fun` and the bundled test is `path_test φ m mM`, whose eight `test_of` obligations all reduce to the corresponding fields of $m$: measurability (`path_test_meas`) by factoring $s\mapsto m(s,\gamma(\varphi\,s))$ as $(s,r)\mapsto m(s,\gamma(r))$ composed with $s\mapsto(s,\varphi\,s)$ and applying `measurableT_comp`; linearity and $\omega$-continuity (`path_test_lin0`, `path_test_linD`, `path_test_linZ`, `path_test_cont`) pointwise, using that the path sup is pointwise $B$'s sup; and the bounds (`path_test_ge0`, `path_test_le1`, `path_test_norm_le`) through `path_norm_ub`. The family is `path_mcone_M Y = {p | ∃ φ m, p = φ ▷ m}`, and the `isMCone` instance on `path_car Ar X B` is assembled from the three axiom proofs below.

> **Paper — §3.2.2 "The measurable cone of paths"** (arXiv 2212.02371 / LMCS 21(1:1), pp. 21–22). So far we have equipped $P$ (the set of measurable paths from $X$ to $C$) with a structure of cone in the algebraic sense of Section 2. We equip now this cone with a measurability structure. This definition will illustrate, for the first time in this paper, the usefulness of the "additional" parameter of tests, spanning measurable spaces taken in $\mathbf{Ar}$. Let $Y\in\mathbf{Ar}$, $\varphi\in\mathbf{Ar}(Y,X)$ and $m\in\mathcal{M}^C_Y$, we define $$\varphi\rhd m : Y\times P\to\mathbb{R}_{\geq 0},\qquad (s,\gamma)\mapsto m(s,\gamma(\varphi(s))).$$ Observe first that for each $s\in Y$, the map $\lambda\gamma\in P\cdot(\varphi\rhd m)(s,\gamma)$ is linear and continuous by linearity and continuity of $m$ in its second argument. We check that the family $(\mathcal{M}_Y\subseteq P'^Y)_{Y\in\mathbf{Ar}}$ defined by $\mathcal{M}_Y=\{\varphi\rhd m\mid\varphi\in\mathbf{Ar}(Y,X)\text{ and }m\in\mathcal{M}^C_Y\}$ is a measurability structure on $P$. […] We use $\mathsf{Path}(X,C)$ for the measurable cone $(P,\mathcal{M})$ defined above.

> **Paper — §3.2.2, the four axioms** (arXiv 2212.02371 / LMCS 21(1:1), pp. 21–22). ▶ **(Msmeas).** Let $p\in\mathcal{M}_Y$ and $\gamma\in P$, so that $p=\varphi\rhd m$ for some $\varphi\in\mathbf{Ar}(Y,X)$ and $m\in\mathcal{M}^C_Y$, then let $\theta=\lambda s\in Y\cdot p(s,\gamma)=\lambda s\in Y\cdot m(s,\gamma(\varphi(s)))$. We know that $\psi=\lambda(s,r)\in Y\times X\cdot m(s,\gamma(r))$ is measurable $Y\times X\to[0,1]$ and hence $\theta=\psi\circ\langle Y,\varphi\rangle$ is measurable $Y\to[0,1]$ since $\varphi$ is measurable. ▶ **(Mscomp).** Let $p\in\mathcal{M}_Y$ and $\psi\in\mathbf{Ar}(Y',Y)$. We have $p=\varphi\rhd m$ for some $\varphi\in\mathbf{Ar}(Y,X)$ and $m\in\mathcal{M}^C_Y$. Then we have $p\circ(\psi\times P)=(\varphi\circ\psi)\rhd(m\circ(\psi\times C))\in\mathcal{M}_{Y'}$. ▶ **(Mssep).** Let $\gamma_1,\gamma_2\in P$ and assume that $\forall p\in\mathcal{M}_0\ p(\gamma_1)=p(\gamma_2)$. Let $r\in X$ that we consider as an element of $\mathbf{Ar}(0,X)$. Let $m\in\mathcal{M}^C_0$, by our assumption we have $(r\rhd m)(\gamma_1)=(r\rhd m)(\gamma_2)$, that is $m(\gamma_1(r))=m(\gamma_2(r))$ and since this holds for all $m\in\mathcal{M}^C_0$ we have $\gamma_1(r)=\gamma_2(r)$ by (Mssep) in $C$. ▶ **(Msnorm).** Let $\gamma\in P\setminus\{0\}$ and $\varepsilon>0$. We can find $r\in X$ such that $\gamma(r)\neq 0$ and $\lVert\gamma\rVert\leq\lVert\gamma(r)\rVert+\frac{\varepsilon}{2}$. By (Msnorm) holding in $C$ we can find $m\in\mathcal{M}^C_0\setminus\{0\}$ such that $\lVert\gamma(r)\rVert\leq\frac{m(\gamma(r))}{\lVert m\rVert}+\frac{\varepsilon}{2}$. Remember that $r\rhd m\in\mathcal{M}_0$ and notice that $\lVert r\rhd m\rVert=\sup\{m(\delta(r))\mid\delta\in\mathbf{B}P\}=\lVert m\rVert$ by Lemma 3.9. So we have $\lVert\gamma\rVert\leq\lVert\gamma(r)\rVert+\frac{\varepsilon}{2}\leq\frac{(r\rhd m)(\gamma)}{\lVert r\rhd m\rVert}+\varepsilon$ and hence $\lVert\gamma\rVert=\sup\{\frac{p(\gamma)}{\lVert p\rVert}\mid p\in\mathcal{M}_0\text{ and }p\neq 0\}$ as required since $\mathcal{M}_0=\{r\rhd m\mid r\in X\text{ and }m\in\mathcal{M}^C_0\}$.

> **Difference — "$r\in X$ considered as an element of $\mathbf{Ar}(0,X)$" is a construction, not a coercion.** (Mssep) is where the paper silently identifies a point $r\in X$ with the constant map $0\to X$. Rocq has no such identification, so `path.v` builds it: `const_r r` is the constant function on `ar_zero Ar`, proved measurable by `measurable_cst` and registered with an `isMeasurableFun` HB instance so that it inhabits `ar_hom Ar (ar_zero Ar) X`. `path_mcone_M_sep` then instantiates the hypothesis at `path_test (const_r r) m mM` for each $r$, reducing to (Mssep) in $B$ pointwise and concluding by `path_eq`. Symmetrically, (Mscomp) needs $\varphi\circ\psi$ to *be* an $\mathbf{Ar}$-morphism: `path_mcone_M_comp` obtains it from mathcomp-analysis's `mfun` composition instance and then closes by `test_eq`, since $p\circ(\psi\times P)$ and $(\varphi\circ\psi)\rhd(\mathrm{test\_reindex}\ \psi\ m)$ are equal only *pointwise*, not definitionally.

> **Difference — (Msnorm): the $\varepsilon$-form, and the degenerate case the paper elides.** As everywhere in this development, `mcone_M_norm` is the $\varepsilon$-approximation form of Remark 3.3, so no normalisation by $\lVert m\rVert$ (and hence no appeal to Lemma 3.9 for $\lVert r\rhd m\rVert=\lVert m\rVert$) is needed. The paper's proof asserts one can find $r$ with *both* $\gamma(r)\neq 0$ and $\lVert\gamma\rVert\leq\lVert\gamma(r)\rVert+\varepsilon/2$. `path_mcone_M_norm` cannot: `sup_adherent` on `path_normset γ` returns some $r_0$ with the norm bound but says nothing about $\gamma(r_0)\neq 0$, so the proof splits. If $\gamma(r_0)\neq 0$ it applies (Msnorm) of $B$ at $\gamma(r_0)$ with $\varepsilon/2$ and returns `path_test (const_r r0) m mM`. If $\gamma(r_0)=0$ then $\lVert\gamma\rVert\leq\varepsilon/2$, and since $\gamma\neq 0$ there is (by `path_eq` and classical choice) some $r_1$ with $\gamma(r_1)\neq 0$; (Msnorm) of $B$ at $\gamma(r_1)$ with $\varepsilon$ then yields a witness whose bound holds for the trivial reason that $\lVert\gamma\rVert\leq\varepsilon/2\leq\varepsilon$ and every test value is non-negative. Note also that the mechanised statement quantifies over the *bundled* test type, so the paper's side condition $m\neq 0$ disappears: it was only needed to make $m/\lVert m\rVert$ meaningful.

```coq
(* theories/mcones/path.v — Section PathTest,
   Variables (R : realType) (Ar : MeasSubcat R) (X : ar_obj Ar)
             (B : MCone.type Ar) (Y : ar_obj Ar) (φ : ar_hom Ar Y X)
             (m : test_of Ar Y B), Hypothesis mM : mcone_M Y m *)
Definition path_test_fun :
    ar_carrier Ar Y -> path_car Ar X B -> R :=
  fun s γ => test_fun m s (path_fun γ (φ s)).

Definition path_test : test_of Ar Y (path_car Ar X B) :=
  MkTestOf path_test_meas path_test_ge0 path_test_le1
           path_test_lin0 path_test_linD path_test_linZ
           path_test_cont path_test_norm_le.

(* Section PathMCone, Variables (R : realType) (Ar : MeasSubcat R)
   (X : ar_obj Ar) (B : MCone.type Ar) *)
Definition path_mcone_M (Y : ar_obj Ar) :
    set (test_of Ar Y (path_car Ar X B)) :=
  [set p | exists (φ : ar_hom Ar Y X) (m : test_of Ar Y B)
                  (mM : mcone_M Y m), p = path_test φ m mM].

Lemma path_mcone_M_comp
  (Y' Y : ar_obj Ar) (ψ : ar_hom Ar Y' Y)
  (p : test_of Ar Y (path_car Ar X B)) :
  path_mcone_M p ->
  path_mcone_M (test_reindex ψ p).

(* Section ConstantArHom, Variable r : ar_carrier Ar X — the point r
   packaged as the constant Ar-morphism 0 -> X the paper writes "r". *)
Definition const_r : ar_hom Ar (ar_zero Ar) X := const_r_fun.

Lemma path_mcone_M_sep (γ1 γ2 : path_car Ar X B) :
  (forall p : test_of Ar (ar_zero Ar) (path_car Ar X B),
    path_mcone_M (Y:=ar_zero Ar) p ->
    test_fun p (ar_zero_pt Ar) γ1 = test_fun p (ar_zero_pt Ar) γ2) ->
  γ1 = γ2.

Lemma path_mcone_M_norm (γ : path_car Ar X B) (eps : R) :
  γ <> path_zero X B -> 0 < eps ->
  exists p : test_of Ar (ar_zero Ar) (path_car Ar X B),
    path_mcone_M (Y:=ar_zero Ar) p /\
    cone_norm γ <= test_fun p (ar_zero_pt Ar) γ + eps.

HB.instance Definition _ (R : realType) (Ar : MeasSubcat R)
    (X : ar_obj Ar) (B : MCone.type Ar) :=
  @isMCone.Build R Ar (path_car Ar X B)
    (@path_mcone_M R Ar X B)
    (@path_mcone_M_comp R Ar X B)
    (@path_mcone_M_sep R Ar X B)
    (@path_mcone_M_norm R Ar X B).
```

With this instance in place, `path_car Ar X B` is a `MCone.type Ar` — which is exactly what paper Thm 4.12 (`path_int_exists`, § 4 below) presupposes when it upgrades $\mathsf{Path}(X,B)$ to an *integrable* cone, and what Lem 3.19's flattening iso is stated between.

### Lem 3.9 (`const_path_measurable`)

Constant functions into a measurable cone are measurable paths — the base case underlying the (Msnorm) argument for the path cone.

> **Paper — Lemma 3.9** (arXiv 2212.02371, `lemma:cst-path`). Let $x\in\underline{C}$ and $\gamma=\boldsymbol\lambda r\in X\cdot x:X\to\underline{C}$ be the constant function. Then $\gamma$ is a measurable path.

```coq
(* theories/mcones/mcone.v — Section Lemma39,
   Variables (R : realType) (Ar : MeasSubcat R) (C : MCone.type Ar) (X : ar_obj Ar) *)
Lemma const_path_measurable (x : C) :
  is_measurable_path (fun _ : ar_carrier Ar X => x).
```

### Lem 3.10 (`reindex_path_measurable`)

Measurable paths are stable under reindexing along an $\mathbf{Ar}$-morphism: precomposing a measurable path with $\phi\in\mathbf{Ar}(Y,X)$ yields a measurable path of arity $Y$.

> **Paper — Lemma 3.10** (arXiv 2212.02371, `lemma:precomp-path`). Let $\gamma:X\to\underline{C}$ be a measurable path and let $\phi\in\mathbf{Ar}(Y,X)$ for some $Y\in\mathbf{Ar}$. Then $\gamma\mathrel{\circ}\phi:Y\to\underline{C}$ is also a measurable path.

```coq
(* theories/mcones/mcone.v — Section Lemma310,
   Variables (R : realType) (Ar : MeasSubcat R) (C : MCone.type Ar)
             (Y X : ar_obj Ar) (γ : ar_carrier Ar X -> C) (φ : ar_hom Ar Y X) *)
Lemma reindex_path_measurable :
  is_measurable_path γ -> is_measurable_path (γ \o φ).
```

### Lem 3.19 (`path_fl_fun`)

Path-flattening: a path of paths $\eta\in\underline{\mathsf{Path}(X,\mathsf{Path}(Y,B))}$ is turned into a bivariate path $\mathrm{fl}_{X,Y}(\eta)=\boldsymbol\lambda(r,s)\cdot\eta(r)(s)$, with `path_fl_inv_fun` the inverse and `path_fl_fun_inv` the bijection identity.

> **Paper — Lemma 3.19** (arXiv 2212.02371, `lemma:meas-path-flat`). There is an iso $\mathrm{fl}_{X,Y}\in\mathbf{MCones}(\mathsf{Path}(X,\mathsf{Path}(Y,B)),\mathsf{Path}(X\times Y,B))$ which flattens $\eta\in\underline{\mathsf{Path}(X,\mathsf{Path}(Y,B))}$ into $\mathrm{fl}_{X,Y}(\eta)=\boldsymbol\lambda (r,s)\in X\times Y\cdot \eta(r)(s)$. As a consequence $\mathrm{fl}_{Y,X}^{-1}\mathrel{\circ}\mathrm{fl}_{X,Y}\in\mathbf{MCones}(\mathsf{Path}(X,\mathsf{Path}(Y,B)),\mathsf{Path}(Y,\mathsf{Path}(X,B)))$, the parameter-swap of a path of paths, is an iso in $\mathbf{MCones}$.

> **Difference.** Only the bivariate function-level content of the iso is proved: the flattening bijection `path_fl_fun` / `path_fl_inv_fun` and the pointwise identity `path_fl_fun_inv`. The full packaging as a `cones_hom` / `mcones_hom` iso — carrying the `ar_prod_carrier_eq` carrier cast, linearity, $\omega$-continuity and the norm equality $\lVert\mathrm{fl}(\eta)\rVert=\lVert\eta\rVert$ — is explicitly deferred (see the notes in `theories/mcones/path.v`). The bivariate form is what the downstream Fubini development (`theories/icones/fubini.v`) actually consumes.

```coq
(* theories/mcones/path.v — Section PathFlatten,
   Variables (R : realType) (Ar : MeasSubcat R)
             (X Y : ar_obj Ar) (B : MCone.type Ar) *)
Definition path_fl_fun (η : path_car Ar X (path_car Ar Y B)) :
    (ar_carrier Ar X * ar_carrier Ar Y)%type -> B :=
  fun p => path_fun (path_fun η p.1) p.2.

Definition path_fl_inv_fun
    (η : (ar_carrier Ar X * ar_carrier Ar Y)%type -> B) :
    ar_carrier Ar X -> ar_carrier Ar Y -> B :=
  fun r s => η (r, s).

Lemma path_fl_fun_inv (η : path_car Ar X (path_car Ar Y B))
  (r : ar_carrier Ar X) (s : ar_carrier Ar Y) :
  path_fl_inv_fun (path_fl_fun η) r s = path_fun (path_fun η r) s.
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
| Lem 4.2 | The integral is norm-bounded: $\lVert\int_X\beta\,d\mu\rVert\leq\lVert\beta\rVert\,\lVert\mu\rVert$ (uniform-bound form). | `path_integral_norm_le` — `theories/icones/icone_integral.v` |
| Lem 4.6 | For a bounded measurable $\varphi:Y\times X\to\mathbb{R}_{\geq 0}$ and a bounded kernel $\kappa:Y\to\mathsf{FMeas}(X)$, the partial integral $s\mapsto\int_X\varphi(s,r)\,\kappa(s)(dr)$ is measurable. | `kernel_integral_measurable` (fine-cast, real-valued), `kernel_integral_measurable_ereal` — `theories/icones/icone_integral.v` |
| Lem 4.7 | The integration operator $\mathcal{I}^{B}_X$ is bilinear (separately linear in the path and the measure), continuous and measurable. | `icone_integral_*` family + `bilin.v` — `theories/icones/icone_integral.v`, `theories/homs/bilin.v` |
| Thm 4.12 | The cone of paths $\mathsf{Path}(X,B)$ into an integrable cone is itself an `ICone`. | the anonymous `isICone` instance built from `path_int_exists` — `theories/icones/examples_icone.v` |
| Thm 4.5 | $\mathsf{FMeas}(X)$ is integrable; the unit cone $1=\perp$ likewise. | `FMeas` is an `ICone`; the `isICone` instance on `cone_one_car Ar` — `theories/icones/examples_icone.v` |
| Cat 4 | The category $\mathbf{ICones}$ has integrable cones and $\mathbf{MCones}$-morphisms preserving the integral. | `icones_hom`, `icones_comp`, `ICones` — `theories/icones/icone_cat.v` |
| Thm 4.15 (Fubini) | The two iterated integrals of a path of paths coincide: $\int_X(\int_Y\dots)\,d\mu = \int_Y(\int_X\dots)\,d\nu$. | `fubini_cone_eq` (paper-form wrapper `fubini_cone_eq_arprod`); supporting `fubini_path_X`/`fubini_path_Y`, `fubini_iter_fun_X` — `theories/icones/fubini.v` |
| Thm 4.16 (ICones complete) | $\mathbf{ICones}$ is complete: it has all small products and all binary equalisers, each with its universal property. | `icones_tuple_unique`, `icones_eq_med_unique` (with `icones_prod`/`icones_eq`, `icones_proj`, `icones_tuple`, `icones_eq_incl`, `icones_eq_med`) — `theories/icones/icone_cat.v` |
| Thm 4.18 | $\mathbf{ICones}$ is well-powered and $1$ is both a separator and a coseparator. | `icones_coseparator`, `icones_separator` — `theories/icones/icone_cat.v`; `icones_well_powered`, `icones_subobject_classP` — `theories/homs/representable.v` |
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

The layer this entry rests on is `theories/icones/pettis.v`, which is Pettis's characterisation on its own, before any integrable-cone structure: `path_integral_eq β µ x` is the Pettis equation itself (also used in the Lem 4.2 entry below), `path_integral_eq_unique` is the (Mssep) uniqueness that makes *the* integral well defined, and `path_integral hex` is the value extracted from an existence witness `hex : exists x, path_integral_eq β µ x`. The § 4 `icone_integral` of this entry is exactly `path_integral` applied to the `isICone` field `icone_exists`, so every Pettis-level fact about a general measurable cone transfers verbatim to integrable cones.

> **Difference.** `path_integral` is *extracted*, not constructed: its body is `proj1_sig (cid hex)`, classical indefinite description applied to the existence witness packaged in the `isICone` mixin. *Why:* building the integral as a term would force a `choiceType` structure on the carrier of every integrable cone on top of its cone data; `cid` keeps the `Precone → Cone → MCone → ICone` tower lightweight and pushes the choice into the ambient classical metatheory. Canonicity is not lost: `path_integral_eq_unique` shows by (Mssep) that any two witnesses of the Pettis equation are equal, so nothing downstream depends on which witness the description operator picks.

```coq
(* theories/icones/pettis.v — Sections PathIntegralUnique / PathIntegralVal,
   Variables (R : realType) (Ar : MeasSubcat R) (B : MCone.type Ar)
             (X : ar_obj Ar) (β : ar_carrier Ar X -> B)
             (µ : fmeas R (ar_carrier Ar X)) *)

Lemma path_integral_eq_unique.

Definition path_integral.
```

### Lem 4.2 (`path_integral_norm_le`)

The integral of a path is bounded in cone-norm: if $\beta$ is integrable over the finite measure $\mu$, then $\lVert\int_X\beta(r)\,\mu(dr)\rVert_B\leq\lVert\beta\rVert_{\mathsf{Path}(X,B)}\,\lVert\mu\rVert_{\mathsf{FMeas}(X)}$. This is the operator-norm bound that underlies boundedness of path-of-paths integrals and the $\omega$-continuity step.

> **Paper — Lemma 4.2** (arXiv 2212.02371, `lemma:integral-bounded`). If $\beta\in\underline{\mathsf{Path}(X,B)}$ is integrable over $\mu\in\mathsf{FMeas}(X)$ then $$\Big\lVert\int_X\beta(r)\mu(dr)\Big\rVert_B\leq\lVert\beta\rVert_{\mathsf{Path}(X,B)}\,\lVert\mu\rVert_{\mathsf{FMeas}(X)}.$$

> **Difference.** The paper phrases the right-hand side with the path-norm $\lVert\beta\rVert_{\mathsf{Path}(X,B)}$ (the sup of $\lVert\beta(r)\rVert$ over the unit ball). The formalization instead takes an *explicit* uniform bound $M_\beta$ with $\forall r\, .\, \lVert\beta(r)\rVert\leq M_\beta$ as a hypothesis and concludes $\lVert x\rVert\leq M_\beta\cdot\lVert\mu\rVert$ for any $x$ that is an integral of $\beta$ over $\mu$ (`path_integral_eq β µ x`). This avoids materialising the path-norm supremum while giving the same bound at every uniform bound $M_\beta$. The proof uses (Msnorm) together with the pointwise `test_norm_le` bound.

```coq
(* theories/icones/icone_integral.v — Section Lemma42,
   Variables (R : realType) (Ar : MeasSubcat R)
             (B : MCone.type Ar) (X : ar_obj Ar)
             (β : ar_carrier Ar X -> B) (µ : fmeas R (ar_carrier Ar X))
             (Mβ : R),
   Hypotheses (Hβ_bound : forall r, cone_norm (β r) <= Mβ)
              (Hβ_meas : is_measurable_path β) *)

Lemma path_integral_norm_le (x : B) :
  path_integral_eq β µ x ->
  (cone_norm x <= Mβ * fmeas_norm µ)%R.
```

### Lem 4.6 (`kernel_integral_measurable`, `kernel_integral_measurable_ereal`)

Integrating a bounded measurable function against a *varying* finite measure leaves the parameter dependence measurable: if $\varphi:Y\times X\to\mathbb{R}_{\geq 0}$ is measurable and bounded and $\kappa:Y\to\mathsf{FMeas}(X)$ is a bounded kernel — measurable evaluation $s\mapsto\kappa(s)(U)$ on every measurable $U$, and uniformly bounded total mass — then $s\mapsto\int_X\varphi(s,r)\,\kappa(s)(dr)$ is measurable. It is the technical prerequisite for Thm 4.12 (paths of paths integrate to paths) and for the joint-measurability half of Lem 4.7, and it is the one place in the development where the mathcomp-analysis finite-kernel library is invoked directly.

> **Paper — Lemma 4.6** (arXiv 2212.02371, § 4; LMCS 21(1:1) pp. 1:24–1:26). Let $\varphi:Y\times X\to\mathbb{R}_{\geq 0}$ be measurable and bounded (say $\varphi\leq M_\varphi$), and let $\kappa:Y\to\mathsf{FMeas}(X)$ be a bounded kernel. Then the partial-integral function $$s\in Y\;\longmapsto\;\int_X\varphi(s,r)\,\kappa(s)(dr)\;\in\;\mathbb{R}_{\geq 0}$$ is measurable.

> **Difference.** The paper proves this by monotone-class reduction: the property holds for simple $\varphi$ and lifts to a general non-negative measurable $\varphi$ by monotone convergence. The formalization instead routes through the mathcomp-analysis HB factory `Kernel_isFinite` — the bounded kernel $\kappa$ is packaged section-locally as an $R$-finite kernel and `measurable_fun_integral_finite_kernel` supplies the $\overline{\mathbb{R}}$-valued statement `kernel_integral_measurable_ereal` — after which the `fine`-cast to $\mathbb{R}$ (`kernel_integral_measurable`) is measurable because the integrand is bounded by $M_\varphi$ and $\kappa$ has uniformly finite total mass. *Why:* reusing the library's kernel theory is shorter than re-running the monotone-class argument, and the kernel structure stays local — downstream consumers see only the two propositional statements. The kernel hypotheses are also given unbundled (a measurability hypothesis plus a uniform mass bound) rather than as a kernel object, so that a plain measurable path of finite measures can be fed in directly.

```coq
(* theories/icones/icone_integral.v — Section Lemma46,
   Variables (R : realType) (d d' : measure_display)
             (X : measurableType d) (Y : measurableType d')
             (κ : Y -> fmeas R X),
   Hypotheses (κ_meas : forall U, measurable U ->
                 measurable_fun setT (fun s => fmeas_mu (κ s) U))
              (κ_bound : exists M : R, forall s, fmeas_norm (κ s) <= M) *)

Lemma kernel_integral_measurable_ereal.

Lemma kernel_integral_measurable.
```

### Lem 4.7 (`icone_integral_*` family + `bilin.v`)

The integration operator $\mathcal{I}^{B}_X$ is bilinear, continuous and measurable. Bilinearity is captured by four equations — additivity and scalar homogeneity separately in the path $\beta$ and in the measure $\mu$ — and continuity is the pair of $\omega$-continuity identities `integral_omega_cont_path` (in $\beta$) and `integral_omega_cont_meas` (in $\mu$): the integral of a supremum of an increasing unit-ball chain *is* the supremum of the integrals, on each side separately. Measurability is `icone_integral_joint_measurable`.

The $\mu$-side linearity is proved one layer down, at the level of the defining `path_integral_eq` witnesses — `path_integral_eq_addmu` and `path_integral_eq_scalemu` — and only then transported to the operator equations, because `icone_integral` is extracted from an existential and the witness form is what the (Mssep) argument consumes. The analytic engine on that side is `integral_meas_sup`, the monotone-convergence step for the *measure* direction: for a non-negative measurable $f$, $\int f\,d\mu_n\to\int f\,d(\sup_n\mu_n)$, obtained by reading the supremum measure as the series of its increments. `precone_residue` is the small `cid`-based utility underneath all of this: it turns the propositional order $x\le y$ into a $\Sigma$-type witness $\{z\mid y=x+z\}$, so that a residue can be chosen pointwise along a chain.

> **Paper — Lemma 4.7** (arXiv 2212.02371, `lemma:int-mesurable`). For each $X\in\mathbf{Ar}$, the map $\mathcal{I}^{B}_X$ is bilinear, continuous and measurable. This means that $\mathcal{I}^{B}_X:\underline{\mathsf{Path}(X,B)}\mathrel{\&}\underline{\mathsf{FMeas}(X)}\to\underline{B}$ is continuous, separately linear in each of its two arguments and that for each $Y\in\mathbf{Ar}$, $\eta\in\underline{\mathsf{Path}(Y,\mathsf{Path}(X,B))}$ and $\kappa\in\underline{\mathsf{Path}(Y,\mathsf{FMeas}(X))}$, the function $\beta=\mathcal{I}^{B}_X\mathrel{\circ}\langle \eta,\kappa\rangle:Y\to\underline{B}$ is a measurable path.

> **Difference.** The single paper lemma is unbundled into named results: separate linearity is the four `icone_integral_addB` / `icone_integral_scaleB` (in $\beta$) and `icone_integral_addmu` / `icone_integral_scalemu` (in $\mu$); continuity is the two $\omega$-continuity identities `integral_omega_cont_path` / `integral_omega_cont_meas`; measurability is `icone_integral_joint_measurable`. *Why:* each fact is consumed independently downstream (and the bilinear packaging lives in `theories/homs/bilin.v`), so it is more convenient to state them one at a time than as one conjunction. Note that `icone_integral_chain_le` — monotonicity of the integral along a chain — is **not** the continuity half of 4.7 but a strictly weaker companion; the equality is carried by the two `integral_omega_cont_*` lemmas.

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
Lemma icone_integral_chain_le : (* monotone along a chain — weaker than continuity *).
Lemma icone_integral_joint_measurable : (* ... *).

(* Section LinearityMu — the µ-linearity at the witness level, which is
   what the (Mssep) argument for the operator equations consumes. *)
Lemma path_integral_eq_addmu : (* witnesses for µ1, µ2 give one for µ1 + µ2 *).
Lemma path_integral_eq_scalemu : (* a witness for µ gives one for r *: µ *).

(* THE continuity half of Lemma 4.7: ω-continuity on each side. *)
Lemma integral_omega_cont_path :
  (* sup of the integrals along a β-chain = integral of the sup path *).
Lemma integral_omega_cont_meas :
  (* sup of the integrals along a µ-chain = integral against the sup measure *).

(* The measure-direction MCT engine behind integral_omega_cont_meas. *)
Lemma integral_meas_sup (f : X -> \bar R) :
  (forall r, 0 <= f r) -> measurable_fun setT f ->
  \int[fmeas_mu (u n)]_(r in [set: X]) f r @[n --> \oo]
    --> \int[fmeas_mu (fmeas_sup_ball uch ub1)]_(r in [set: X]) f r.

(* Section PreconeResidue — the Σ-type form of the precone order. *)
Lemma precone_residue (x y : P) :
  precone_le x y -> { z : P | y = (x + z)%PC }.
```

### Thm 4.5 / 4.12 (`path_int_exists`, `FMeas`/unit `isICone` instances)

The two archetypal integrable cones are exhibited: the cone of finite measures $\mathsf{FMeas}(X)$ (Thm 4.5) and, for any integrable $B$, the cone of measurable paths $\mathsf{Path}(X,B)$ (Thm 4.12), whose integral is computed pointwise. The same file also installs the `isICone` instance on the unit cone $1=\perp$. The `isICone` mixin asks for one existence witness, so each theorem is delivered as exactly one lemma feeding one `HB.instance`: `fmeas_int_exists` for Thm 4.5 (built from the concrete integral `fmeas_int` and its Pettis equation `fmeas_int_pettis`) and `path_int_exists` for Thm 4.12. The two `HB.instance Definition _` lines that register them are anonymous, so the instances have no citable name of their own — the lemma names above are what the rest of the development refers to.

> **Paper — Theorem 4.5** (arXiv 2212.02371). For each measurable space $X$, the measurable cone $\mathsf{FMeas}(X)$ is integrable.

> **Paper — Theorem 4.12** (arXiv 2212.02371). For each $X\in\mathbf{Ar}$ and each integrable cone $B$, the measurable cone $\mathsf{Path}(X,B)$ is integrable.

```coq
(* theories/icones/examples_icone.v *)

(* Paper Thm 4.5: the isICone witness for FMeas(X). *)
Lemma fmeas_int_exists
    (X' : ar_obj Ar)
    (β : ar_carrier Ar X' -> T) :
  is_measurable_path β ->
  forall µ : fmeas R (ar_carrier Ar X'),
    is_path_integrable β µ.

(* Paper Thm 4.12: the isICone witness for Path(X,B). *)
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

### Thm 4.15 Fubini (`fubini_cone_eq`)

The Fubini theorem for cones: the two iterated integrals of a path of paths coincide in $B$. Integrating $\beta$ first over $X$ against $\mu$ and then over $Y$ against $\nu$ yields the same element of $B$ as integrating first over $Y$ against $\nu$ and then over $X$ against $\mu$. The headline identity is `fubini_cone_eq`; the paper-form wrapper `fubini_cone_eq_arprod` takes a genuine measurable path $\beta$ on the product arity $X\times Y$.

> **Paper — Theorem 4.15** (arXiv 2212.02371, `th:paths-Fubini`). Let $X,Y\in\mathbf{Ar}$, $\eta\in\underline{\mathsf{Path}(X,\mathsf{Path}(Y,B))}$, $\mu\in\underline{\mathsf{FMeas}(X)}$ and $\nu\in\underline{\mathsf{FMeas}(Y)}$. We have $$\int_Y\Big(\int_X\eta(r)\mu(dr)\Big)(s)\,\nu(ds)=\int_{X\times Y}\mathsf{fl}(\eta)(t)\,(\mu\times\nu)(dt).$$

> **Difference.** Because the `ar_prod_carrier_eq` cast into the product arity is not transparent in the formalization, `fubini_cone_eq` states the equation cast-free, directly between the two iterations for $\beta : X\times Y\to B$ (via the iterated paths `fubini_path_X`/`fubini_path_Y`), rather than routing through the bridging product integral $\int_{X\times Y}\mathsf{fl}(\eta)\,d(\mu\times\nu)$. The proof goes through the scalar Tonelli lemmas (`fubini_tonelli1`/`fubini_tonelli2`) on each arity-$0$ test and promotes to $B$ by separation (`mcone_M_sep`). The paper-form statement, for a measurable path $\beta$ on the product arity, is the wrapper `fubini_cone_eq_arprod`. Those "cast-measurability helpers" are exactly the five `beta_uncast_*` lemmas: `beta_uncast` reindexes $\beta$ through `ar_prod_cast` onto the bare product of carriers, and `beta_uncast_bound`, `beta_uncast_secY`, `beta_uncast_secX`, `beta_uncast_jointX`, `beta_uncast_jointY` re-derive, one by one, the uniform bound, the two section-measurability hypotheses and the two joint test-measurability hypotheses (in the $X$- and $Y$-iteration argument orders) that `fubini_cone_eq` asks for — so the cast is paid for once, here, and never again inside the Fubini proof. The inner-integral apparatus `fubini_iter_fun_X` (with `fubini_iter_fun_X_norm_le` bounding its norm by Lemma 4.2 and `fubini_iter_fun_X_is_path` proving it is a measurable path) supports `fubini_path_X`.

```coq
(* theories/icones/fubini.v — Section Fubini415, Variables
   (R : realType) (Ar : MeasSubcat R)
   (B : ICone.type Ar) (X Y : ar_obj Ar)
   (β : (ar_carrier Ar X * ar_carrier Ar Y)%type -> B) (Mβ : R),
   Hypotheses HMβ : forall p, cone_norm (β p) <= Mβ;
   Hβx : forall x, is_measurable_path (fun y => β (x, y));
   Hβy : forall y, is_measurable_path (fun x => β (x, y));
   Variables (µ : fmeas R (ar_carrier Ar X)) (ν : fmeas R (ar_carrier Ar Y)) *)

Definition fubini_path_X : ar_carrier Ar X -> B :=
  fubini_iter_fun_X β Hβx ν.
Definition fubini_path_Y : ar_carrier Ar Y -> B :=
  fubini_iter_fun_Y β Hβy µ.

Lemma fubini_cone_eq :
  icone_integral fubini_path_X fubini_path_X_meas µ =
  icone_integral fubini_path_Y fubini_path_Y_meas ν.

(* Section Fubini415Arprod, β : ar_carrier Ar (ar_prod Ar X Y) -> B,
   Hβ : is_measurable_path β *)

(* The cast-free reindexing of β, and the five facts about it that
   discharge the hypotheses of fubini_cone_eq from is_measurable_path β. *)
Definition beta_uncast : (ar_carrier Ar X * ar_carrier Ar Y)%type -> B :=
  fun p => β (ar_prod_cast p).

Lemma beta_uncast_bound  : (* a uniform norm bound, inherited from β *).
Lemma beta_uncast_secY   : (* y ↦ β (x, y) is a measurable path, x fixed *).
Lemma beta_uncast_secX   : (* x ↦ β (x, y) is a measurable path, y fixed *).
Lemma beta_uncast_jointX : (* joint test-measurability, (z,(x,y)) shape *).
Lemma beta_uncast_jointY : (* joint test-measurability, (z,(y,x)) shape *).

Lemma fubini_cone_eq_arprod
    (Mβ : R)
    (HMβ : forall p : ar_carrier Ar (ar_prod Ar X Y),
             (cone_norm (β p) <= Mβ)%R) :
  icone_integral (fubini_path_X beta_uncast ν) _ µ =
  icone_integral (fubini_path_Y beta_uncast µ) _ ν.
```

### Thm 4.16 ICones complete (`icones_tuple_unique`, `icones_eq_med_unique`)

The category $\mathbf{ICones}$ is complete. Completeness is mechanised through the two universal properties it reduces to: all small products and all binary equalisers, each supplied with its full universal property. The product of a family $(B_i)_{i\in I}$ is `icones_prod` with projections `icones_proj`, tupling `icones_tuple`, factorization `icones_tuple_proj` and uniqueness `icones_tuple_unique`; the equaliser of $f,g:B\to C$ is `icones_eq` with inclusion `icones_eq_incl`, mediating map `icones_eq_med`, factorization `icones_eq_med_factor` and uniqueness `icones_eq_med_unique`. The two uniqueness lemmas are the concrete witnesses of the limit universal properties.

> **Paper — Theorem 4.16** (arXiv 2212.02371, `th:mcones-complete`). The category $\mathbf{ICones}$ is complete.

> **Difference.** The paper reads "$\mathbf{ICones}$ is complete" as having all small products together with all binary equalisers; the mechanisation provides exactly those data as two universal-property packages, each with existence, factorization and uniqueness. The completeness statement is thus mechanised piecewise (products + equalisers) rather than as a single "has all small limits" object.

```coq
(* theories/icones/icone_cat.v *)

Definition icones_prod (R : realType) (Ar : MeasSubcat R)
  (I : Type) (B : I -> ICone.type Ar) : ICone.type Ar := (* ... *).

(* Section IConesProductsUniversal, Variables I B (Q : ICone.type Ar)
   (f : forall i, icones_hom Ar Q (icones_prod B)) *)
Definition icones_proj (i : I) : icones_hom Ar (icones_prod B) (B i).
Definition icones_tuple : icones_hom Ar Q (icones_prod B).

Lemma icones_tuple_proj (i : I) :
  icones_comp (icones_proj i) icones_tuple = f i.

Lemma icones_tuple_unique (h : icones_hom Ar Q (icones_prod B)) :
  (forall i, icones_comp (icones_proj i) h = f i) ->
  h = icones_tuple.

Definition icones_eq (R : realType) (Ar : MeasSubcat R)
  (B C : ICone.type Ar) (f g : icones_hom Ar B C) : ICone.type Ar := (* ... *).

(* Section IConesEqualisersUniversal, Variables B C f g (T : ICone.type Ar)
   (h : icones_hom Ar T B) (Hh : icones_comp f h = icones_comp g h) *)
Definition icones_eq_incl : icones_hom Ar (icones_eq f g) B.
Definition icones_eq_med : icones_hom Ar T (icones_eq f g).

Lemma icones_eq_med_factor :
  icones_comp icones_eq_incl icones_eq_med = h.

Lemma icones_eq_med_unique (h' : icones_hom Ar T (icones_eq f g)) :
  icones_comp icones_eq_incl h' = h ->
  h' = icones_eq_med.
```

### Thm 4.18 (`icones_coseparator`, `icones_separator`, `icones_well_powered`)

In $\mathbf{ICones}$ the unit cone $1$ is both a separator and a coseparator, and the category is well-powered. All three conjuncts are formalized: `icones_coseparator` records that $1$ is a coseparator (two morphisms agree iff every arity-$0$ test of the codomain agrees on their images at every point), `icones_separator` records that $1$ is a separator (two morphisms agree iff they agree at every point), and `icones_well_powered` discharges well-poweredness by exhibiting a small classifying `Type` (`SubobjClassifier`) into which subobjects inject up to iso (`icones_subobject_classP`). `icones_subobject_inj` is the elementary reading of a subobject that the well-poweredness argument starts from: an injective `icones_hom` is determined *as a function* by its image, so a subobject of $B$ is faithfully described by data on $B$ — which is what makes the classifier's fields (a subset of $B$ plus the transported operations) sufficient.

> **Paper — Theorem 4.18** (arXiv 2212.02371, `th:icones-conditions-saft`). In the category $\mathbf{ICones}$ the object $1$ is a coseparator and a separator and $\mathbf{ICones}$ is well-powered.

> **Difference.** The paper's separator/coseparator phrasings are given in the practical test-family form: tests at arity $0$ *are* the elements of $\mathbf{ICones}(C,1)$ in this encoding, so "$1$ is a coseparator" becomes `icones_coseparator` ($f=g$ iff every arity-$0$ test of $C$ agrees on $f\,x$, $g\,x$ for all $x$) and "$1$ is a separator" becomes `icones_separator` ($f=g$ iff $f\,x=g\,x$ for all $x$). Well-poweredness is recast as the existence of a small classifying `Type` `SubobjClassifier` that identifies subobjects up to iso (`icones_subobject_classP`) — the exact input the special adjoint functor theorem then consumes (see *Beyond the paper* below).

```coq
(* theories/icones/icone_cat.v — Sections IConesCoseparator / IConesSeparator,
   Variables (R : realType) (Ar : MeasSubcat R), B C : ICone.type Ar *)

Lemma icones_coseparator (f g : icones_hom Ar B C) :
  (forall x : B,
    forall m : test_of Ar (ar_zero Ar) C,
      mcone_M (ar_zero Ar) m ->
      test_fun m (ar_zero_pt Ar)
        (cones_hom_fun (mcones_hom_cones (icones_hom_mcones f)) x) =
      test_fun m (ar_zero_pt Ar)
        (cones_hom_fun (mcones_hom_cones (icones_hom_mcones g)) x)) ->
  f = g.

Lemma icones_separator (f g : icones_hom Ar B C) :
  (forall x : B,
    cones_hom_fun (mcones_hom_cones (icones_hom_mcones f)) x =
    cones_hom_fun (mcones_hom_cones (icones_hom_mcones g)) x) ->
  f = g.

(* Section IConesWellPowered — an injective icones_hom is determined,
   as a function, by its image: the subobject reading of a mono. *)
Lemma icones_subobject_inj (A : ICone.type Ar) (h : icones_hom Ar A B) :
  injective (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))) ->
  forall (a1 a2 : A), (* ... a1 = a2 *) True.

(* theories/homs/representable.v — Section Classifier,
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

### Thm 4.19 (`is_icones_left_adjoint`, `wi_obj`, `wi_med`, `wi_med_unique`)

Every limit-preserving functor out of $\mathbf{ICones}$ has a left adjoint, by SAFT with the § 4 inputs: completeness (Thm 4.16) and the coseparator + well-poweredness (Thm 4.18). The formalization records the *conclusion* as the hom-bijection contract `is_icones_left_adjoint` — a candidate left adjoint $F$ to $R$ is one equipped with mutually inverse maps $\Phi : \mathbf{ICones}(F c, x) \simeq \mathcal{C}(c, R\,x) : \Psi$ — and mechanises the SAFT construction that produces it: the wide intersection `wi_obj` of a small family of subobjects, with its mediating morphism `wi_med` and the uniqueness `wi_med_unique` that makes it initial.

> **Paper — Theorem 4.19** (arXiv 2212.02371, `th:Icones-adjoint-functor`). If $\mathcal{C}$ is a locally small category and $R:\mathbf{ICones}\to\mathcal{C}$ is a functor which preserves all limits, then $R$ has a left adjoint. *Proof.* Apply the special adjoint functor theorem.

> **Difference.** The paper's one-line proof invokes SAFT as a black box; the development contains no single theorem quantifying over an arbitrary locally small $\mathcal{C}$. Instead the SAFT *argument* is mechanised as a reusable engine (subobject classifier, wide intersections with their universal property — see *Beyond the paper*), and the two instances the paper actually consumes are built concretely against the `is_icones_left_adjoint` contract: the tensor ${-}\otimes C \dashv C \multimap {-}$ (`tensor_curry` / `tensor_uncurry` with proved round-trips, `tensor_construct.v`) and the exponential $\mathsf{E} \dashv \mathsf{Der}$ (`Bang`, `nl` / `lin`, `bang_construct.v`). The remark's third instance (integral completion of a measurable cone along $\mathbf{ICones}\to\mathbf{MCones}$) is not used by §§ 5–9 and is not constructed.

```coq
(* theories/homs/representable.v — Section SAFTExport *)
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

(* theories/homs/representable.v — Section WideIntersection *)
Definition wi_med : icones_hom Ar Z wi_obj :=
  icones_eq_med wi_u wi_v wi_tuple wi_tuple_equ.

Lemma wi_med_unique (kk : icones_hom Ar Z wi_obj) :
  (forall k, icones_comp (wi_proj k) kk = ff k) ->
  kk = wi_med.
```

---

## Paper § 5 — Internal hom, tensor, and SMCC

| Paper | English statement | Rocq |
|---|---|---|
| Lem 5.3 | Argument-swapping iso $\mathsf{sw}$ across a path: $f\mapsto\lambda r.\lambda x.\,f(x)(r)$ (the path-preservation core is packaged). | `swap_lin_path` — `theories/homs/tensor_hom_iso.v` |
| Lem 5.4 / Def 5.7 | The internal hom $C\multimap D$ carrier (the integrable cone of $\mathbf{ICones}$-morphisms $C\to D$); its action $(h\multimap g):(C_1\multimap D_1)\to(C_2\multimap D_2)$ by $(h\multimap g)(f)=g\circ f\circ h$. | `linhom_car`, `linhom_postc`, `linhom_prec`, `linhom_map_fun` — `theories/homs/linhom.v` |
| § 5.1 precone layer | The pointwise algebra on $C\multimap D$: zero, sum and non-negative scalar action are computed pointwise in $D$, and all eleven `isPrecone` fields transfer pointwise through extensionality of the carrier. | `linhom_pre`, `linhom_zero`, `linhom_add`, `linhom_scale`, `linhom_eq`, `linhom_pos` — `theories/homs/linhom.v` (Section `LinhomPrecone`) |
| § 5.1 cone layer | The operator norm $\lVert f\rVert=\sup\{\lVert f(x)\rVert\mid\lVert x\rVert\le 1\}$ as a genuine real supremum, with its upper-bound and least-upper-bound properties, and the four norm axioms (Normh), (Normz), (Normt), (Normp). | `linhom_norm`, `linhom_norm_sup_ub`, `linhom_norm_sup_lub`, `linhom_normh`, `linhom_normz`, `linhom_normt`, `linhom_normp` — `theories/homs/linhom.v` (Section `LinhomNorm`, Section `LinhomConeAxioms`) |
| § 5.1 Normc | The $\omega$-completeness axiom on $C\multimap D$: the pointwise supremum of a $\preceq$-increasing unit-ball chain of integrable linear maps is again one, and it is the least upper bound. | `linhom_sup_unit`, `linhom_sup_fun`, `linhom_sup_ball`, `linhom_sup_ball_ub`, `linhom_sup_ball_lub` — `theories/homs/linhom.v` (Section `LinhomSupBall`, Section `LinhomSupBallOrder`) |
| § 5.1 difference helper | Given $u,v:C\multimap D$ with $\lVert v\rVert\le 1$ and a per-point witness of $v(x)=u(x)+z$, the difference $v-u$ is packaged once as a full `linhom_car`, discharging the five carrier fields by cancellation in $D$. | `linhom_diff_fun`, `linhom_diff_E`, `linhom_diff_car` — `theories/homs/linhom.v` (Section `LinhomDiff`, Section `LinhomDiffPack`) |
| § 5.1 diagonal sup | Two cone-level structural identities the (Normc) proof rests on: the diagonal sum of two unit-ball chains has the sum of the sups as its sup, and iterated unit-ball suprema commute. | `cone_sup_ball_addD`, `cone_sup_ball_addD_le`, `cone_sup_ball_addD_ge`, `cone_sup_ball_swap` — `theories/homs/linhom.v`; general-radius originals in `theories/cones/omega_general.v` |
| § 5.1 mcone layer | The measurability structure on $C\multimap D$: tests are the $\gamma\triangleright m$ family $(s,f)\mapsto m(s,f(\gamma(s)))$ for unit-ball paths $\gamma$, and this family satisfies (Mscomp), (Mssep) and (Msnorm). | `linhom_test`, `linhom_mcone_M`, `linhom_mcone_M_comp`, `linhom_mcone_M_sep`, `linhom_mcone_M_norm` — `theories/homs/linhom.v` (Section `LinhomTest`, Section `LinhomMCone`) |
| Lem 5.4 icone layer | The mechanised content of Lem 5.4: the pointwise Pettis integral $\bar\eta(x)=\int\eta(r)(x)\,\mu(dr)$ is a `linhom_car`, and it satisfies the Pettis equation for every $\gamma\triangleright m$ — so $C\multimap D$ is integrable. | `linhom_int_fun`, `linhom_int_pt_meas`, `linhom_int_fun_pres_int`, `linhom_int_car_pettis`, `linhom_int_exists` — `theories/homs/linhom.v` (Section `LinhomICone`) |
| Lem 5.5 | Argument-swapping natural iso $\mathsf{sw}':B_1\multimap(B_2\multimap C)\to B_2\multimap(B_1\multimap C)$, $f\mapsto\lambda x_1.\lambda x_2.\,f(x_1)(x_2)$. | `swap_lin_lin_hom` — `theories/homs/tensor_iso.v` |
| Def 5.6 | The cone of integrable bilinear maps $(C_1,C_2)\multimap D=C_1\multimap(C_2\multimap D)$. | `bilin_data`, `bilin_to_curried`, `curried_to_bilin`, `bilin_to_linhom`, `linhom_to_bilin` — `theories/homs/linhom.v` |
| § 5.3 test-pullback | The "equivalently" clause of Def 3.13, packaged for reuse: a target test pulled back along an $\mathbf{MCones}$ morphism stays jointly measurable (basic and bivariate shapes), and commutes with unit-ball suprema. | `test_pullback_meas`, `test_pullback_meas_bivar`, `test_pullback_cont`, `test_of_sup` — `theories/icones/test_pullback.v` |
| Prop 5.8 | The internal-hom action $h\multimap g$ lifts to an $\mathbf{ICones}$ morphism. | `linhom_map_icones` — `theories/homs/linhom_functor.v` |
| Prop 5.8 functoriality | The one-sided actions $C\multimap g$ and $h\multimap D$ with their computation laws, and the two functor laws making $\multimap:\mathbf{ICones}^{\mathrm{op}}\times\mathbf{ICones}\to\mathbf{ICones}$ a functor. | `linhom_post_icones`, `linhom_pre_icones`, `linhom_map_icones_id`, `linhom_map_icones_comp` — `theories/homs/linhom_functor.v`; object-level `linhom_map_funE`, `linhom_map_id`, `linhom_map_comp` — `theories/homs/linhom.v` |
| ICones isos | The isomorphism record in $\mathbf{ICones}$ used to state every structural equivalence of § 5 and § 9: forward and backward morphisms plus the two round-trips, two smart constructors, the groupoid laws and bijectivity of the underlying map. | `icones_iso`, `icones_isoP`, `icones_iso_of_cancel`, `icones_iso_refl`, `icones_iso_sym`, `icones_iso_trans`, `iso_fwd_bij` — `theories/homs/icones_iso.v` |
| Thm 5.9 | The functor $C\multimap{-}$ preserves all limits (hence has a left adjoint). | `limpl_preserves_prod`, `limpl_preserves_limits` — `theories/homs/limpl_continuous.v` |
| Lem 5.10 | Swap of the two hom-arguments across a path: $f\mapsto\lambda(y,r,x).\,f(x,r,y)$. | `lfun_path_swap` — `theories/homs/tensor_iso.v` |
| Lem 5.11 | A bounded $\eta:X\to(B\otimes C)\multimap 1$ is a path once its pure-tensor evaluations are measurable. | `path_tens_to_X`, `path_tens_to_X_unit` — `theories/homs/tensor_iso.v` (proved at an arbitrary integrable codomain $D$; the paper's scalar statement is the $D:=1$ instance) |
| § 5.4 tau | The universal map $\tau_{B,C}=\Phi_{B,C,B\otimes C}(\mathrm{Id}_{B\otimes C})$ and the pure tensor $x\otimes y=\tau_{B,C}(x)(y)$ — what the `⊗p` notation of this chapter's snippets denotes. | `tau`, `ptensor`, `ptensorE` — `theories/homs/tensor.v` |
| Eq 5.1 | The hom-bijection factors through $\tau$: $\Phi_{B,C,D}(f)=(C\multimap f)\circ\tau_{B,C}$, pointwise $\Phi(f)(x)(y)=f(x\otimes y)$; with the naturality of $\Phi$ it rests on. | `tensor_curry_factor`, `tensor_curryE` — `theories/homs/tensor.v`; `tensor_curry_natural_post`, `tensor_curry_natural_D`, `tensor_curry_natural_B` — `theories/homs/tensor_construct.v` |
| § 5.4 bifunctor | The action of $\otimes$ on morphisms: $f\otimes g$, its identity law, its pure-tensor computation law $(f\otimes g)(x\otimes y)=(f\,x)\otimes(g\,y)$, and the composition law. | `tensor_mor`, `tensor_mor_id` — `theories/homs/tensor.v`; `tensor_morE` — `theories/homs/smcc.v`; `tensor_mor_comp` — `theories/cbv/em_cartesian.v` |
| § 5.4 bilinearity | The pure tensor is bilinear: a non-negative scalar commutes through either slot, and it is additive in the right slot. | `ptensorZl`, `ptensorZr`, `linhom_funZ` — `theories/homs/smcc.v`; `ptensorDr` — `theories/programs/infra/cbv_anchors.v` |
| Thm 5.12 | The currying isomorphism $(B\otimes C)\multimap D\;\simeq\;B\multimap(C\multimap D)$, its forward/backward maps and their bijectivity, and morphism-level injectivity of $\Phi$. | `tensor_hom_iso` — `theories/homs/tensor_iso.v`; `tensor_hom_Phi`, `tensor_hom_fwd`, `tensor_hom_bwd`, `tensor_hom_fwd_bij`, `tensor_curry_inj` — `theories/homs/tensor.v` |
| Thm 5.13 | Norm identity for pure tensors: $\lVert x\otimes y\rVert=\lVert x\rVert\,\lVert y\rVert$. | `tensor_norm_le` ($\le$) + the $\ge$ direction via Prop 3.11 — `theories/homs/tensor.v` / `tensor_iso.v` |
| Prop 5.14 | A morphism out of an iterated tensor is determined on pure tensors $x\otimes y$. | `tensor_ext`, `tensor_ext3`, `tensor_ext4` — `theories/homs/tensor.v`, `theories/homs/smcc.v` |
| Eqs 5.2–5.4 | The structural isos $\alpha$, $\lambda$, $\rho$, $\gamma$ of the monoidal structure, each with its pure-tensor computation law. | `tensor_assoc`, `tensor_lunit`, `tensor_runit`, `tensor_braid`, `tensor_assocEp`, `tensor_lunitEp`, `tensor_runitEp`, `tensor_braidEp` — `theories/homs/smcc.v`; the underlying isos and their computation laws `tensor_assoc_iso`, `tensor_lunit_iso`, `tensor_runit_iso`, `tensor_braid_iso`, `tensor_assocE`, `tensor_lunitE`, `tensor_runitE`, `tensor_braidE` — `theories/homs/tensor_iso.v` |
| § 5.5 coherence | The symmetry law and the triangle, pentagon and braiding-hexagon diagrams are **proved** — by pure-tensor extensionality (Prop 5.14) from Eqs 5.2–5.4 — not assumed. | `tensor_braid_invol`, `tensor_triangle`, `tensor_pentagon`, `tensor_hexagon` — `theories/homs/smcc.v` |
| Thm 5.15 | $(\mathbf{ICones},\otimes,1)$ is a symmetric monoidal closed category. | `ICones_SMCC`, `ICones_smcc` — `theories/homs/smcc.v` |
| Rem 5.1 | The tensor object is given by SAFT, without an explicit carrier. | The paper's invocation of SAFT is *mechanised* concretely in `representable.v` + `tensor_construct.v` — see *Beyond the paper* below |

### Lem 5.3 (`swap_lin_path`)

The argument-swapping isomorphism $\mathsf{sw}$ carries a morphism $f\in\mathbf{MCones}\big(C\multimap\mathrm{Path}(X,D)\big)$ to $\lambda r.\lambda x.\,f(x)(r)\in\mathrm{Path}(X,C\multimap D)$; the load-bearing content is that the *diagonal evaluation* along a unit-ball path stays a measurable path.

> **Paper — Lemma 5.3** (arXiv 2212.02371, `lemma:swap-lin-path`). There is an argument swapping isomorphism $\mathsf{sw}\in\mathbf{MCones}\big((C\multimap\mathrm{Path}(X,D)),\ \mathrm{Path}(X,C\multimap D)\big)$ which maps $f$ to $\lambda r.\lambda x.\,f(x)(r)$.

> **Difference.** Only the measurability core of the swap is packaged: given a measurable path $\Phi:X\to(C\multimap E)$ and a $C$-path $\gamma$ with $\lVert\gamma\rVert\le 1$, the diagonal evaluation $r\mapsto\Phi(r)(\gamma(r))$ is a measurable path in $E$ (`swap_lin_path`). The full bidirectional $\mathbf{MCones}$ iso record is not separately packaged; this measurability lemma is exactly the path-preservation half that the rest of § 5 consumes (e.g. `swap_lin_pres_path`, `lfun_path_swap`).

```coq
(* theories/homs/tensor_hom_iso.v — Section SwapLinPath,
   Variables (R : realType) (Ar : MeasSubcat R), C E : ICone.type Ar,
   X : ar_obj Ar, Φ : ar_carrier Ar X -> linhom_car Ar C E,
   γ : path_car Ar X C, HΦ : is_measurable_path Φ, γub : cone_norm γ <= 1 *)
Lemma swap_lin_path :
  is_measurable_path (fun r => linhom_fun (Φ r) (path_fun γ r)).
```

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

`linhom_car` is a *two-layer* record on purpose. The inner `linhom_pre` carries the four properties that make no reference to integration — linearity, $\omega$-continuity, boundedness on the unit ball, and preservation of measurable paths — and `linhom_car` adds integral preservation as a fifth field on top. The split is forced by dependency, not taste: the *type* of the integral-preservation field mentions the path-preservation field (`linhom_pre_pres_path` supplies the `is_measurable_path` argument that `icone_integral` demands on the right-hand side), so the two cannot sit in one flat record. This is the same layering the base categories use, `cones_hom → mcones_hom → icones_hom`.

The single carrier `linhom_car Ar C D` then climbs the whole tower `Precone → Cone → MCone → ICone` inside `theories/homs/linhom.v`, one `HB.instance` per layer, each documented in its own entry below: pointwise algebra (*§ 5.1 precone layer*), the canonical-sup operator norm with (Normh)/(Normz)/(Normt)/(Normp)/(Normc) (*§ 5.1 cone layer*, *§ 5.1 Normc*), the $\gamma\triangleright m$ test family with (Mscomp)/(Mssep)/(Msnorm) (*§ 5.1 mcone layer*), and the pointwise Pettis integral (*Lem 5.4 icone layer*). Three sanity-check sections in the same file — `LinhomConeCheck`, `LinhomMConeCheck`, `LinhomIConeCheck` — type-check `linhom_car Ar C D : coneType R`, `: mconeType Ar` and `: iconeType Ar` respectively, so each layer is confirmed to be *found by canonical-structure inference*, not merely proved.

> **Paper — § 5.1** (arXiv 2212.02371 / LMCS 21(1:1), "The cone of linear morphisms"). Let $C$ and $D$ be objects of $\mathbf{ICones}$ and let $P$ be the set of all $f:C\to D$ such that, for some $\varepsilon>0$, one has $\varepsilon f\in\mathbf{ICones}(C,D)$, equipped with the same algebraic structure as $C\multimap D$ (see Lemma 2.13). This makes sense since the algebraic laws of the cone $C\multimap D$ preserve measurability and since integration is linear.

> **Difference.** The paper defines the carrier by the *scaling* condition "$\varepsilon f\in\mathbf{ICones}(C,D)$ for some $\varepsilon>0$"; `linhom_car` instead bundles the equivalent unfolded reading — $\mathbb{R}_{\ge0}$-linear, $\omega$-continuous, bounded on the unit ball, path-preserving, integral-preserving — as five record fields. The two agree because an $\mathbf{ICones}$ morphism is exactly a norm-$\le 1$ map with those properties, so an $\varepsilon$-witness is interchangeable with an explicit bound; carrying the bound directly avoids threading an existential $\varepsilon$ through every downstream field proof, and it is the bound (not $\varepsilon$) that the norm and the (Normc) construction consume.

> **Difference.** *The $(\lVert x\rVert+1)$-scaling pattern.* Many proofs about $C\multimap D$ cannot work at an arbitrary $x\in C$ directly, because the measurability and supremum machinery of a cone is stated on the *unit ball*. The file therefore uses one uniform trick throughout: put $S:=\lVert x\rVert+1$ and $x':=S^{-1}\cdot x$ (so $\lVert x'\rVert\le 1$), do the work at $x'$, and rescale by $S$. The $+1$ — rather than the mathematically natural $\lVert x\rVert$ — is what makes the recipe total: it keeps $S$ invertible in the degenerate case $\lVert x\rVert=0$. The named occurrences are `linhom_sup_fun` (step 1 of (Normc)), `linhom_mcone_M_sep` ((Mssep), via a constant path at $x'$), `linhom_int_pt_meas` (pointwise measurability of the integral), and the path-preservation / joint-measurability lemmas of the same file. The supporting arithmetic is packaged once as `cnorm_succ_nng` / `cnorm_succ_inv_nng` / `cnorm_succ_scaleK` / `cnorm_inv_unit`.

```coq
(* theories/homs/linhom.v — Section LinhomPre *)
Record linhom_pre.
```

```coq
(* theories/homs/linhom.v — Section LinhomSupBall *)
(* the (‖x‖+1)-rescaling kit shared by (Normc), (Mssep) and the integral *)
Definition cnorm_succ_nng.
Definition cnorm_succ_inv_nng.
Lemma cnorm_succ_scaleK.
Lemma cnorm_inv_unit.
```

### § 5.1 precone layer (`linhom_pre`, `linhom_zero`, `linhom_add`, `linhom_scale`, `linhom_eq`, `linhom_pos`)

The first layer of the tower on $C\multimap D$ is purely algebraic. The zero map, the pointwise sum $f+g$ and the pointwise scalar action $r\cdot f$ are each *packaged as full `linhom_car`s* — that is, each of the five carrier fields (linearity, $\omega$-continuity, ball-boundedness, path preservation, integral preservation) is re-proved for the result, which is what `linhom_zero` / `linhom_add` / `linhom_scale` do via their `_fun_*` companions. The eleven `isPrecone` obligations then all collapse to the corresponding axiom of $D$ read at a point: `linhom_addA`, `linhom_addC`, `linhom_add0`, `linhom_scale_DAr`, `linhom_scale_DAl`, `linhom_scale_A`, `linhom_scale_1`, `linhom_scale_0r`, `linhom_scale_0l`, `linhom_cancel` and `linhom_pos`. The single tool that makes this mechanical is the extensionality lemma `linhom_eq`: two elements of $C\multimap D$ are equal as soon as their underlying functions agree pointwise (the remaining record fields are `Prop`s, discharged by proof irrelevance). The layer is closed by the file's `isPrecone.Build` instance, which takes those eleven lemmas as its fields; being an `HB.instance Definition _` it is anonymous and has no citable name of its own — audit it through the lemmas it consumes.

> **Paper — § 5.1** (arXiv 2212.02371 / LMCS 21(1:1), "The cone of linear morphisms"). … equipped with the same algebraic structure as $C\multimap D$ (see Lemma 2.13). This makes sense since the algebraic laws of the cone $C\multimap D$ preserve measurability and since integration is linear.

> **Difference.** The paper obtains the algebra by *importing* it from the $\mathbf{Cones}$-level linear hom of Lemma 2.13 and then observing that the extra properties survive. The mechanisation has no such inheritance step — `linhom_car` is a fresh record, so each pointwise operation is rebuilt from scratch and every closure property is a named lemma (`linhom_add_fun_linear`, `linhom_add_fun_continuous`, `linhom_add_fun_bounded`, `linhom_add_fun_pres_path`, `linhom_add_fun_pres_int`, and the `linhom_scale_fun_*` family). The observation the paper compresses into one sentence is therefore a block of ten field proofs here; nothing is assumed.

```coq
(* theories/homs/linhom.v — Section LinhomCar *)
Lemma linhom_eq.
```

```coq
(* theories/homs/linhom.v — Section LinhomZero *)
Definition linhom_zero.
```

```coq
(* theories/homs/linhom.v — Section LinhomAlgPack *)
Definition linhom_add.
Definition linhom_scale.
```

```coq
(* theories/homs/linhom.v — Section LinhomPrecone *)
(* the last two of the eleven isPrecone obligations; the other nine
   (addA/addC/add0/scale_DAr/scale_DAl/scale_A/scale_1/scale_0r/scale_0l)
   have the same one-line shape *)
Lemma linhom_cancel.
Lemma linhom_pos.
```

### § 5.1 cone layer (`linhom_norm`, `linhom_norm_sup_ub`, `linhom_norm_sup_lub`, `linhom_normh`, `linhom_normz`, `linhom_normt`, `linhom_normp`)

The norm of $f\in C\multimap D$ is the operator norm $\lVert f\rVert=\sup\{\lVert f(x)\rVert\mid \lVert x\rVert\le 1\}$, defined as the *actual* real supremum of the image set `linhom_normset f`. The set is non-empty (it contains $\lVert f(0)\rVert=0$, `linhom_normset_nonempty`) and bounded above — the witness is `linmap_norm`, the `cid`-extracted bound of Lem 2.11, applied to the underlying linear map (`linhom_normset_has_ubound`) — so Dedekind completeness of $\mathbb{R}$ gives the sup (`linhom_normset_has_sup`). Both halves of the universal property are then available as lemmas: `linhom_norm_sup_ub` ($\lVert f(x)\rVert\le\lVert f\rVert$ for $\lVert x\rVert\le 1$) and `linhom_norm_sup_lub` (any competing bound dominates $\lVert f\rVert$). With those, the four algebraic norm axioms are short: `linhom_normh` (homogeneity, by pushing the scalar through the sup, with a separate $r=0$ branch), `linhom_normz` ($\lVert f\rVert=0\Rightarrow f=0$, from (Normz) in $D$ at the rescaled point, extended to all of $C$ by linearity), `linhom_normt` (triangle inequality, pointwise) and `linhom_normp` (monotonicity under $\preceq$, via `linhom_le_pointwise` and (Normp) of $D$).

> **Paper — § 5.1** (arXiv 2212.02371 / LMCS 21(1:1), "The cone of linear morphisms"). … such that $\lVert f_n\rVert\le 1$ (remember that $\lVert f\rVert=\sup_{x\in\mathcal{B}C}\lVert f(x)\rVert$) …

> **Difference.** *Why a canonical sup here and only a bound in § 2.* Lem 2.11's `linmap_norm` extracts, by `cid`, *an* upper bound of $\{\lVert f(x)\rVert\mid\lVert x\rVert\le1\}$; that is all the $\mathbf{Cones}$-level hom needs, since (Normh) there only has to be *a* norm making the axioms hold. It is the wrong shape for the internal hom: the (Normc) axiom on $C\multimap D$ needs the upper-bound *and* least-upper-bound properties simultaneously — the sup of a chain must be shown both above every $f_n$ and below every competing bound — and it needs them in a form that survives the $\omega$-continuity argument for the sup-of-chain operator. Hence `linhom_norm` is the genuine `sup`, with `linhom_norm_sup_ub` / `linhom_norm_sup_lub` as its two faces; `linmap_norm` survives here only as the boundedness witness that proves the sup exists.

```coq
(* theories/homs/linhom.v — Section LinhomNorm *)
Definition linhom_normset.
Lemma linhom_normset_has_sup.
Definition linhom_norm.
Lemma linhom_norm_sup_ub.
Lemma linhom_norm_sup_lub.
```

```coq
(* theories/homs/linhom.v — Section LinhomLePointwise *)
Lemma linhom_le_pointwise.
```

```coq
(* theories/homs/linhom.v — Section LinhomConeAxioms *)
Lemma linhom_normh.
Lemma linhom_normz.
Lemma linhom_normt.
Lemma linhom_normp.
```

### § 5.1 Normc (`linhom_sup_unit`, `linhom_sup_fun`, `linhom_sup_ball`, `linhom_sup_ball_ub`, `linhom_sup_ball_lub`)

(Normc) asks that a $\preceq$-increasing chain $(f_n)_n$ in the unit ball of $C\multimap D$ have a least upper bound there. The construction is in two steps. *On the unit ball:* for $\lVert x\rVert\le 1$ each $f_n(x)$ lies in $\mathcal{B}D$ and the chain $(f_n(x))_n$ is increasing (`linhom_le_pointwise`), so $D$'s own (Normc) supplies $\bigvee_n f_n(x)$ — this is `linhom_sup_unit`. *Off the unit ball:* for an arbitrary $x$ put $S:=\lVert x\rVert+1$ and define $\bigl(\bigvee_n f_n\bigr)(x):=S\cdot\bigvee_n f_n(S^{-1}x)$, which is `linhom_sup_fun`; `linhom_sup_fun_unitE` checks that this agrees with `linhom_sup_unit` where both apply. The body of the argument is then the six field-inheritance lemmas: linearity at $0$, $+$ and $\cdot$ (`linhom_sup_fun_lin0`, `linhom_sup_fun_linD` — the delicate one, which applies the diagonal-sup identity at the common factor $S=\lVert x\rVert+\lVert y\rVert+1$ — and `linhom_sup_fun_linZ`), ball-boundedness with $M=1$ (`linhom_sup_fun_bounded`), $\omega$-continuity (`linhom_sup_fun_continuous`, which is where `cone_sup_ball_swap` is used to exchange the chain index with the argument index), path preservation (`linhom_sup_fun_pres_path`) and integral preservation (`linhom_sup_fun_pres_int`, by monotone convergence under the integral in $D$). The result is packaged as a full `linhom_car` by `linhom_sup_ball`, with `linhom_sup_ball_norm` giving $\lVert\bigvee_n f_n\rVert\le 1$; `linhom_sup_ball_ub` and `linhom_sup_ball_lub` are the two order facts that close (Normc). Immediately after them the file's (anonymous) `isCone.Build` instance registers `linhom_car Ar C D : coneType R`, taking `linhom_norm` together with the four axioms of the previous entry and these two lemmas as its fields; the section `LinhomConeCheck` type-checks the result.

> **Paper — § 5.1** (arXiv 2212.02371 / LMCS 21(1:1), "The cone of linear morphisms"). Moreover given an increasing sequence $(f_n)_{n\in\mathbb{N}}$ of measurable and integral preserving elements of $C\multimap D$ such that $\lVert f_n\rVert\le 1$ (remember that $\lVert f\rVert=\sup_{x\in\mathcal{B}C}\lVert f(x)\rVert$), the linear and continuous map $f=\sup_{n\in\mathbb{N}}f_n$ is measurable and preserves integrals by the monotone convergence theorem, as we show now.

> **Difference.** The paper writes $f=\sup_{n}f_n$ and reasons about it directly, because in set-theoretic prose the pointwise sup of an increasing bounded family of functions simply *exists*. In the formalisation `cone_sup_ball` is only available for a chain in the *unit ball*, so the sup has to be built in the two steps above and its five carrier fields proved one at a time; the $(\lVert x\rVert+1)$-rescaling that bridges the two steps is the pattern documented on the *Lem 5.4 / Def 5.7* entry. The paper's own "measurable and preserves integrals by the monotone convergence theorem" is `linhom_sup_fun_pres_path` and `linhom_sup_fun_pres_int`, in that order.

```coq
(* theories/homs/linhom.v — Section LinhomSupBall *)
Definition linhom_sup_unit.
Definition linhom_sup_fun.
Lemma linhom_sup_fun_unitE.

(* the six field-inheritance lemmas *)
Lemma linhom_sup_fun_lin0.
Lemma linhom_sup_fun_linD.
Lemma linhom_sup_fun_linZ.
Lemma linhom_sup_fun_bounded.
Lemma linhom_sup_fun_continuous.
Lemma linhom_sup_fun_pres_path.
Lemma linhom_sup_fun_pres_int.
```

```coq
(* theories/homs/linhom.v — Section LinhomSupPack *)
Definition linhom_sup_ball.
Lemma linhom_sup_ball_norm.
```

```coq
(* theories/homs/linhom.v — Section LinhomSupBallOrder *)
Lemma linhom_sup_ball_ub.
Lemma linhom_sup_ball_lub.
```

### § 5.1 difference helper (`linhom_diff_fun`, `linhom_diff_E`, `linhom_diff_car`)

Both halves of (Normc) have the same algebraic shape: to prove $u\preceq v$ in $C\multimap D$ one must *exhibit* a difference, i.e. an element $\delta$ of $C\multimap D$ with $v=u+\delta$ — the order on a precone is defined by the existence of such a witness, not by an inequality. `linhom_diff_car` packages that construction once. Given $u,v:C\multimap D$ with $\lVert v\rVert\le 1$ and, for every $x$, *some* $z\in D$ with $v(x)=u(x)+z$, it produces a full `linhom_car` $\delta$: the underlying function `linhom_diff_fun` is obtained by classical indefinite description (`cid`) on the per-point witness, `linhom_diff_E` is its defining equation $v(x)=u(x)+\delta(x)$, and the five carrier fields are then discharged by cancellation in $D$ — linearity by cancelling $u$ against the linearity of $v$ (`linhom_diff_linear`); ball-boundedness from $\delta(x)\preceq v(x)$ and (Normp) of $D$ (`linhom_diff_bounded`); $\omega$-continuity from the continuity of $u$ and $v$ on the chain plus the diagonal-sup identity and (Cancel) of $D$ (`linhom_diff_continuous`); path preservation pointwise via `measurable_funB` (`linhom_diff_pres_path`); and integral preservation from that of $u$ and $v$ together with additivity of the Pettis integral in the path argument, `path_integral_eq_addB` (`linhom_diff_pres_int`).

> **Difference.** This helper has no counterpart in the paper, which states $\preceq$ as an order and never has to produce the witness. It exists because the two (Normc) obligations `linhom_sup_ball_ub` and `linhom_sup_ball_lub` would otherwise repeat the same five field proofs verbatim; factoring them out is what keeps that part of the file finite. The hypothesis $\lVert v\rVert\le 1$ is not decoration: it is consumed by the $\omega$-continuity step, to keep the chain $\delta(x_n)$ inside the unit ball where `cone_sup_ball` is defined.

```coq
(* theories/homs/linhom.v — Section LinhomDiff *)
Definition linhom_diff_fun.
Lemma linhom_diff_E.
Lemma linhom_diff_linear.
```

```coq
(* theories/homs/linhom.v — Section LinhomDiffPack *)
Lemma linhom_diff_bounded.
Lemma linhom_diff_continuous.
Lemma linhom_diff_pres_path.
Lemma linhom_diff_pres_int.
Definition linhom_diff_car.
```

### § 5.1 diagonal sup (`cone_sup_ball_addD`, `cone_sup_ball_addD_le`, `cone_sup_ball_addD_ge`, `cone_sup_ball_swap`)

Two facts about suprema in an arbitrary cone carry the (Normc) proof on $C\multimap D$, and neither is in the paper's § 5.1 text — it treats both as evident. The *diagonal-sup identity* `cone_sup_ball_addD` says that for two $\preceq$-increasing unit-ball chains $(a_n)_n,(b_n)_n$ whose diagonal sum $(a_n+b_n)_n$ is itself increasing and unit-ball, $\bigvee_n(a_n+b_n)=\bigvee_n a_n+\bigvee_n b_n$; it is what makes the additive half of the pointwise sup linear (`linhom_sup_fun_linD`) and what powers the cancellation in `linhom_diff_continuous`. It is split into `cone_sup_ball_addD_le` (immediate from `cone_sup_ball_lub`: witnesses above $a_n$ and $b_n$ sum to a witness above $a_n+b_n$) and the substantive `cone_sup_ball_addD_ge`, where every cross-term $a_n+b_k$ is dominated by $a_m+b_m$ at $m=\max(n,k)$ — hence by the diagonal sup, hence of norm $\le 1$ — after which *two* applications of the one-sided identity `sup_at_addr` (the radius-general form of `sup_ball_addr`), with the summands exchanged between them, reduce the claim to that chain of cross-terms. The *sup-swap identity* `cone_sup_ball_swap` says that the two iterated unit-ball suprema of a doubly-indexed increasing family agree; it is the engine of `linhom_sup_fun_continuous`.

> **Difference.** These lemmas are now *proved once, at an arbitrary radius*, in `theories/cones/omega_general.v` (`cone_sup_at_addD`, and the radius-1 corollaries `cone_sup_ball_addD` / `_le` / `_ge` / `cone_sup_ball_swap`). What `theories/homs/linhom.v` declares under the same four names are thin re-exports — `Proof. exact: omega_general.cone_sup_ball_addD. Qed.` and friends — kept because they state the identity in the exact shape § 5.1 consumes, so the `isPrecone`/`isCone` instances below them read unchanged. Cite whichever file matches the client you are auditing; the mathematical content lives in `omega_general.v`, which also subsumes the two earlier copies `sup_ball_addD` (`totmono.v`) and `sh_sup_swap` (`stablehom.v`).

```coq
(* theories/homs/linhom.v — Section DiagonalSup / Section DiagonalSupEq *)
Lemma cone_sup_ball_addD_le.
Lemma cone_sup_ball_addD_ge.
Lemma cone_sup_ball_addD.
```

```coq
(* theories/homs/linhom.v — Section LinhomSupCont *)
Lemma cone_sup_ball_swap (b : nat -> nat -> D)
    (b_row_ch : forall k n, b n k <=p b n.+1 k)
    (b_col_ch : forall n k, b n k <=p b n k.+1)
    (b_ub : forall n k, cnorm (b n k) <= 1)
    (b_col_sup_ub : forall n,
       cnorm
         (cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k)) <= 1)
    (b_col_sup_ch : forall n,
       cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k) <=p
       cone_sup_ball (b n.+1) (b_col_ch n.+1) (fun k => b_ub n.+1 k))
    (b_row_sup_ub : forall k,
       cnorm (cone_sup_ball (b^~ k) (b_row_ch k) (fun n => b_ub n k))
       <= 1)
    (b_row_sup_ch : forall k,
       cone_sup_ball (b^~ k) (b_row_ch k) (fun n => b_ub n k) <=p
       cone_sup_ball (b^~ k.+1) (b_row_ch k.+1) (fun n => b_ub n k.+1)) :
  cone_sup_ball
    (fun n => cone_sup_ball (b n) (b_col_ch n) (fun k => b_ub n k))
    b_col_sup_ch b_col_sup_ub =
  cone_sup_ball
    (fun k => cone_sup_ball (b^~ k) (b_row_ch k) (fun n => b_ub n k))
    b_row_sup_ch b_row_sup_ub.
```

### § 5.1 mcone layer (`linhom_test`, `linhom_mcone_M`, `linhom_mcone_M_comp`, `linhom_mcone_M_sep`, `linhom_mcone_M_norm`)

The measurability structure on $C\multimap D$ is built from the tests of $D$ and the paths of $C$: for $Y\in\mathbf{Ar}$, a measurable path $\gamma\in\mathsf{Path}(Y,C)$ with $\lVert\gamma\rVert\le 1$ and a test $m\in\mathcal{M}^{D}_Y$, the test $\gamma\triangleright m$ evaluates $f$ along $\gamma$ and measures the result, $(\gamma\triangleright m)(s,f)=m(s,f(\gamma(s)))$. `linhom_test` is that test with all eight `test_of` obligations discharged — measurability (`linhom_test_meas`, by post-composing $\gamma$ with $f$ into a $D$-path and taking the diagonal section of the resulting joint measurability), non-negativity and the $[0,1]$ bound, linearity in $f$, continuity, and the norm bound `linhom_test_norm_le`. `linhom_mcone_M Y` is the set of all such tests, and the three closure axioms are: (Mscomp) `linhom_mcone_M_comp`, where reindexing along $\psi:Y'\to Y$ returns $(\gamma\circ\psi)\triangleright(m\circ(\psi\times D))$ — of the required shape, with the unit-ball constraint preserved because the image of $\gamma\circ\psi$ is contained in that of $\gamma$; (Mssep) `linhom_mcone_M_sep`, which separates $f_1,f_2$ pointwise by testing against the *constant* path at the rescaled $x'=(\lVert x\rVert+1)^{-1}x$ and rescaling back by linearity, then invoking (Mssep) in $D$; and (Msnorm) `linhom_mcone_M_norm`, the paper's $\varepsilon/3$-then-$\varepsilon/2$ argument — pick $x\in\mathcal{B}C$ with $\lVert f\rVert\le\lVert f(x)\rVert+\varepsilon/3$, then $m$ by (Msnorm) in $D$, and combine. The three lemmas are the fields of the file's (anonymous) `isMCone.Build` instance, which registers `linhom_car Ar C D : mconeType Ar`; the section `LinhomMConeCheck` type-checks it.

> **Paper — § 5.1** (arXiv 2212.02371 / LMCS 21(1:1), "The cone of linear morphisms"). Given $\gamma\in\mathsf{Path}(X,C)$ and $m\in\mathcal{M}^{D}_X$ we define $\gamma\triangleright m=\boldsymbol\lambda(r,f)\in X\times P\cdot m(r,f(\gamma(r))):X\times P\to\mathbb{R}_{\ge 0}$. For each $r\in X$ the function $l=(\gamma\triangleright m)(r,\_):C\multimap D\to\mathbb{R}_{\ge 0}$ is linear and continuous by linearity and continuity of $m$ in its second argument. We define $\mathcal{M}_X=\{\gamma\triangleright m\mid\gamma\in\mathsf{Path}(X,C)\text{ and }m\in\mathcal{M}^{D}_X\}$. […] So we have defined a measurable cone that we denote as $C\multimap D$.

> **Difference.** The paper's $\mathcal{M}_X$ ranges over *all* $\gamma\in\mathsf{Path}(X,C)$; `linhom_mcone_M` additionally requires $\lVert\gamma\rVert\le 1$. The restriction is forced by the `test_of` record, whose `test_le1` field demands $m(r,x)\le 1$ for every $x$ in the unit ball: since $\lVert f(\gamma(s))\rVert\le\lVert f\rVert\,\lVert\gamma(s)\rVert$, a test built from an unbounded $\gamma$ would not be $[0,1]$-valued on $\mathcal{B}(C\multimap D)$, and the paper's own (Msmeas) check ("the fact that $\varphi$ ranges in $[0,1]$ results from the assumption that $\lVert f\rVert\le 1$") tacitly assumes it. Nothing is lost: (Msnorm) only ever needs the constant path at a unit-ball point, and (Mscomp) preserves the constraint.

> **Difference.** This layer is *not* one of the paper's numbered results — § 5.1 establishes it in running text and closes with "So we have defined a measurable cone that we denote as $C\multimap D$". (Paper Lemma 5.3 is the argument-swapping iso $\mathsf{sw}$, documented separately above.)

```coq
(* theories/homs/linhom.v — Section LinhomTest *)
Definition linhom_test_fun.
Lemma linhom_test_meas.
Lemma linhom_test_norm_le.
Definition linhom_test.
```

```coq
(* theories/homs/linhom.v — Section LinhomMCone *)
Definition linhom_mcone_M.
Lemma linhom_mcone_M_comp.
Lemma linhom_mcone_M_sep.
Lemma linhom_mcone_M_norm.
```

### Lem 5.4 icone layer (`linhom_int_fun`, `linhom_int_pt_meas`, `linhom_int_fun_pres_int`, `linhom_int_car_pettis`, `linhom_int_exists`)

This is the mechanised content of Lem 5.4. Fix an arity $Y'$, a measurable path $\eta:Y'\to(C\multimap D)$ and a finite measure $\mu$; the candidate integral is taken *pointwise in $D$*, $\bar\eta(x):=\int_{Y'}\eta(r)(x)\,\mu(dr)$ — that is `linhom_int_fun`. It is well formed because for each $x$ the map $r\mapsto\eta(r)(x)$ is a measurable path of $D$ (`linhom_int_pt_meas`: rescale $x$ into the unit ball, then apply (Msmeas) to $\eta$ against the test $\gamma_{x'}\triangleright m_D$ built from the constant path at $x'$). The five carrier fields follow: boundedness $\lVert\bar\eta(x)\rVert\le\lVert\eta\rVert\lVert\mu\rVert$ from `path_integral_norm_le` (`linhom_int_fun_bounded`); linearity from the Pettis-equation bilinearity lemmas `path_integral_eq_addB` / `path_integral_eq_scaleB` on the integrand plus linearity of each $\eta(r)$, all under `icone_integral_eqP` (`linhom_int_fun_linear`); $\omega$-continuity by monotone convergence in $D$ along $r\mapsto\eta(r)(x_n)$ (`linhom_int_fun_continuous`); path preservation from the joint measurability lemma `linhom_int_fun_joint_meas` (`linhom_int_fun_pres_path`); and integral preservation `linhom_int_fun_pres_int`, the Fubini step, where both sides of $\bar\eta(\int\beta\,d\nu)=\int\bar\eta(\beta(\cdot))\,d\nu$ unfold to the two iterated integrals of one path of paths over $X\times Y'$ and are identified by `fubini_cone_eq` (Thm 4.15). Finally `linhom_int_car_pettis` checks that the packaged `linhom_int_car` satisfies the Pettis equation against every test $\gamma\triangleright m$ of the § 5.1 mcone layer, and `linhom_int_exists` is the `is_path_integrable` witness that the file's (anonymous) `isICone.Build` instance consumes to register `linhom_car Ar C D : iconeType Ar` — the fourth and last rung of the tower, type-checked by the section `LinhomIConeCheck`.

> **Paper — Lemma 5.4** (arXiv 2212.02371 / LMCS 21(1:1)). The measurable cone $C\multimap D$ is integrable.

> **Paper — Lemma 5.4, proof** (arXiv 2212.02371 / LMCS 21(1:1)). Let $X\in\mathbf{Ar}$, $\eta\in\mathsf{Path}(X,C\multimap D)$ and $\mu\in\mathsf{FMeas}(X)$. Let $f=\boldsymbol\lambda x\in C\cdot\int^{D}\eta(r)(x)\mu(dr)=\boldsymbol\lambda x\in C\cdot\int^{D}\mathsf{sw}(\eta)(x)(r)\mu(dr)$. […] Let $p\in\mathcal{M}^{C\multimap D}_0$. Let $x\in C$ and $m\in\mathcal{M}^{D}_0$ be such that $p=x\triangleright m$, we have $p(f)=m\bigl(\int^{D}\eta(r)(x)\mu(dr)\bigr)=\int m(\eta(r)(x))\mu(dr)=\int p(\eta(r))\mu(dr)$, so $\eta$ is integrable over $\mu$, and $\int^{C\multimap D}\eta(r)\mu(dr)=f$.

> **Difference.** The paper routes every measurability obligation of Lem 5.4 through the swapping iso $\mathsf{sw}$ of Lem 5.3 (writing $\bar\eta(x)$ as $\int\mathsf{sw}(\eta)(x)(r)\mu(dr)$, so that $\mathsf{sw}(\eta)\circ\gamma\in\mathsf{Path}(Y,\mathsf{Path}(X,D))$ makes Lem 4.7 and Thm 4.15 directly applicable). The mechanisation cannot: `swap_lin_path` is *stated about* `linhom_car` and therefore lives downstream, in `theories/homs/tensor_hom_iso.v`, which `linhom.v` may not import. So the two measurability steps are proved directly against the $\gamma\triangleright m$ test family instead — `linhom_int_pt_meas` for pointwise measurability and `linhom_int_fun_joint_meas` for the joint form — while the Fubini step is exactly the paper's, `fubini_cone_eq` at the path of paths $\beta_2$. The closing Pettis computation is transcribed unchanged as `linhom_int_car_pettis`.

```coq
(* theories/homs/linhom.v — Section LinhomIntFun *)
Lemma linhom_int_pt_meas.
Definition linhom_int_fun.
Lemma linhom_int_fun_bounded.
Lemma linhom_int_fun_linear.
Lemma linhom_int_fun_joint_meas.
Lemma linhom_int_fun_pres_path.
Lemma linhom_int_fun_continuous.
Lemma linhom_int_fun_pres_int.
Definition linhom_int_car.
Lemma linhom_int_car_pettis.
```

```coq
(* theories/homs/linhom.v — Section LinhomICone *)
Lemma linhom_int_exists.
```

### Lem 5.5 (`swap_lin_lin_hom`)

The argument-swapping natural isomorphism $\mathsf{sw}'$ transposes an iterated hom, carrying $f\in\mathbf{ICones}\big(B_1\multimap(B_2\multimap C)\big)$ to $\lambda x_1.\lambda x_2.\,f(x_1)(x_2)\in B_2\multimap(B_1\multimap C)$. It is what builds the braiding $\sigma$ of the tensor.

> **Paper — Lemma 5.5** (arXiv 2212.02371, `lemma:swap-lin-lin`). There is an argument swapping natural isomorphism $\mathsf{sw}'\in\mathbf{ICones}\big(B_1\multimap(B_2\multimap C),\ B_2\multimap(B_1\multimap C)\big)$ which maps $f$ to $\lambda x_1.\lambda x_2.\,f(x_1)(x_2)$.

> **Difference.** The mechanisation packages the transpose *morphism* `swap_lin_lin_hom` together with its computation law `swap_lin_lin_homE` — both directions of the paper iso are the same construction, being involutive — rather than a bidirectional `icones_iso` record. This is exactly the ingredient used to define the braiding: `braid_g := swap_lin_lin_hom (tauL B A)`.

```coq
(* theories/homs/tensor_iso.v — Section SwapLinLin2,
   Variables (R : realType) (Ar : MeasSubcat R), (B1 B2 C : ICone.type Ar),
   f : icones_hom Ar B1 (linhom_car Ar B2 C) *)
Definition swap_lin_lin_hom : icones_hom Ar B2 (linhom_car Ar B1 C) :=
  MkIConesHom swap_lin_mcones swap_lin_pres_int.

Lemma swap_lin_lin_homE (b2 : B2) (b1 : B1) :
  linhom_fun (swap_lin_lin_hom b2) b1 = linhom_fun (f b1) b2.
```

### Def 5.6 (`bilin_data`, `bilin_to_curried`, `curried_to_bilin`)

The cone of integrable bilinear and continuous maps $C_1,C_2\to D$ is defined as the iterated hom $(C_1,C_2)\multimap D=C_1\multimap(C_2\multimap D)$.

> **Paper — Definition 5.6** (arXiv 2212.02371, `def:bilinear`). Let $C_1,C_2,D$ be integrable cones. We define $(C_1,C_2)\multimap D=C_1\multimap(C_2\multimap D)$ and call this integrable cone the cone of integrable bilinear and continuous maps $C_1,C_2\to D$.

> **Difference.** The paper defines the object as the literal iterated hom $C_1\multimap(C_2\multimap D)$. The mechanisation packages the *separately-linear* presentation `bilin_data` — the underlying $C_1\to C_2\to D$ function bundled with its left section (`bilin_left`, a $C_2\multimap D$ for each $x_1$) and right section (`bilin_right`, a $C_1\multimap D$ for each $x_2$), both agreeing with `bilin_fun` — plus the curry/uncurry round-trips `bilin_to_curried` / `curried_to_bilin` realising the identity $(C_1,C_2)\multimap D=C_1\multimap(C_2\multimap D)$.

```coq
(* theories/homs/linhom.v — Section Bilin,
   Variables (R : realType) (Ar : MeasSubcat R), C1 C2 D : ICone.type Ar *)
Record bilin_data : Type := MkBilin {
  bilin_fun :> C1 -> C2 -> D;
  bilin_left : forall x1 : C1, linhom_car Ar C2 D;
  bilin_left_eq :
    forall (x1 : C1) (x2 : C2),
      linhom_fun (bilin_left x1) x2 = bilin_fun x1 x2;
  bilin_right : forall x2 : C2, linhom_car Ar C1 D;
  bilin_right_eq :
    forall (x1 : C1) (x2 : C2),
      linhom_fun (bilin_right x2) x1 = bilin_fun x1 x2;
}.

(* curry / uncurry round-trips (Section CurriedBilin) *)
Definition bilin_to_curried (f : bilin_data Ar C1 C2 D) :
    C1 -> linhom_car Ar C2 D :=
  fun x1 => bilin_left f x1.

Definition curried_to_bilin
  (F : C1 -> linhom_car Ar C2 D)
  (Hright : forall x2 : C2, linhom_car Ar C1 D)
  (Hright_eq :
    forall (x1 : C1) (x2 : C2),
      linhom_fun (Hright x2) x1 = linhom_fun (F x1) x2) :
  bilin_data Ar C1 C2 D :=
  MkBilin (fun x1 x2 => linhom_fun (F x1) x2)
          F (fun x1 x2 => erefl _) Hright Hright_eq.
```

Downstream clients do not consume `bilin_to_curried` / `curried_to_bilin` under those names: `theories/homs/linhom.v` re-exports them as `bilin_to_linhom` (curry) and `linhom_to_bilin` (uncurry) — the paper-aligned spelling of Def 5.6 — together with the two round-trip equations that make the correspondence usable in rewriting. `bilin_to_linhom_E` says $\mathtt{bilin\_to\_linhom}(f)(x_1)(x_2)=f(x_1,x_2)$ (it *is* the `bilin_left_eq` field of the datum), and `linhom_to_bilin_E` says $\mathtt{linhom\_to\_bilin}(F,H_{\mathrm{right}})(x_1,x_2)=F(x_1)(x_2)$ (definitional). With the full HB tower on `linhom_car` in place, both maps are maps between integrable cones, which is what upgrades this function-level bijection to the categorical statement of Thm 5.12.

> **Paper — § 5.2** (arXiv 2212.02371 / LMCS 21(1:1), after Definition 5.6). Indeed, thanks to Lemma 2.19, an element of $C_1,C_2\multimap D$ can be seen as a function $f:C_1\mathbin{\&}C_2\to D$ which is separately linear and $\omega$-continuous. […] Last the integral of a measurable path $\eta\in\mathsf{Path}(X,(C_1,C_2\multimap D))$ over $\mu\in\mathsf{FMeas}(X)$ is characterized by $\bigl(\int\eta(r)\mu(dr)\bigr)(x_1,x_2)=\int\eta(r)(x_1,x_2)\mu(dr)$.

> **Difference.** The round-trips are delivered *at the function level* only. That is exactly the interface Thm 6.5 needs — its faithfulness and fullness halves consume the two equations at Dirac paths — and the morphism-level upgrade is not re-proved here but obtained from Thm 5.12. Note also that `linhom_to_bilin` is not an inverse of `bilin_to_linhom` on the nose: uncurrying requires the *right*-section data $H_{\mathrm{right}}$ as an extra argument, because a bare $F:C_1\to(C_2\multimap D)$ carries no witness that $x_1\mapsto F(x_1)(x_2)$ is again a `linhom_car`.

```coq
(* theories/homs/linhom.v — Section BilinLinhomAlias *)
Definition bilin_to_linhom.
Definition linhom_to_bilin.
Lemma bilin_to_linhom_E.
Lemma linhom_to_bilin_E.
```

### § 5.3 test-pullback (`test_pullback_meas`, `test_pullback_meas_bivar`, `test_pullback_cont`)

Definition 3.13 characterises an $\mathbf{MCones}$ morphism twice over: as a $\mathbf{Cones}$ morphism that sends measurable paths to measurable paths, and — the paper's "equivalently" — by the joint measurability of every *target* test pulled back along it. The forward direction of that second reading is what § 5.3 actually consumes: it is the tool that lifts the internal-hom action $h\multimap g$ to an $\mathbf{ICones}$ morphism (Prop 5.8). `theories/icones/test_pullback.v` packages it in the two shapes those proofs need — the basic section `test_pullback_meas` for a single path argument $\varphi$, and the bivariate `test_pullback_meas_bivar`, where the path argument is folded out of a pair $(s,r)\in Z\times W$ through `ar_prod` — plus the continuity companion `test_pullback_cont`.

> **Paper — Definition 3.13** (arXiv 2212.02371). The category $\mathbf{MCones}$ has measurable cones as objects and an element of $\mathbf{MCones}(B,C)$ is an $f\in\mathbf{Cones}(\underline{B},\underline{C})$ such that for each $X\in\mathbf{Ar}$ and each measurable path $\beta:X\to\underline{B}$ the function $f\mathrel{\circ}\beta$ is a measurable path. Equivalently $$\forall Y\in\mathbf{Ar}\ \forall m\in\mathcal{M}^{C}_Y\quad\boldsymbol\lambda (s,r)\in{X\times Y}\cdot m(s,f(\beta(r)))\text{ is measurable.}$$

> **Difference.** Only the **forward** direction of the paper's "equivalently" is packaged (path preservation $\Rightarrow$ test measurability). *Why:* `mcones_hom` carries path preservation as a field (`mcones_hom_pres_path`), so the converse is never needed downstream; every consumer wants the test-side reading of a morphism it already has. Three further encoding points: (i) the mechanised product is ordered (test arity) $\times$ (path arity) — it follows the paper's binder $(s,r)$ rather than the paper's displayed $X\times Y$, which transposes it; (ii) `test_pullback_cont` is stated for a bare `cones_hom` between measurable cones — linearity, norm-decrease and $\omega$-continuity are all it uses of the morphism — so it serves the `cones_hom` layer of Prop 5.8, before the `mcones_hom` structure is built; (iii) the file sits in `theories/icones/` rather than with the other `MCones` material, because the proof of the basic section goes through `measurable_test_path_section` of `theories/icones/icone_integral.v`.

Both measurability shapes reduce to `measurable_test_path_section` applied to the post-composed path $g\circ\varphi$, whose measurability is exactly `mcones_hom_pres_path g` (isolated as `test_pullback_path`). The bivariate version first reindexes the test $m$ along `ar_prod_fst` to a test at the product arity `ar_prod Z W`, applies the basic section, then folds the input pair back through the `ar_prod_cast` / `test_reindex` pattern also used in `bilin.v` and `linhom.v`. `test_pullback_section` is the $r$-marginal at a fixed test index.

```coq
(* theories/icones/test_pullback.v — Section TestPullback,
   Variables (R : realType) (Ar : MeasSubcat R), (B C : MCone.type Ar),
   g : mcones_hom Ar B C *)
Lemma test_pullback_path.

Lemma test_pullback_meas.

Lemma test_pullback_section.

Lemma test_pullback_meas_bivar.
```

The continuity half is assembled from three small facts about a `cones_hom` $g$: the $g$-image of a $\preceq$-increasing unit-ball chain is again a $\preceq$-increasing unit-ball chain, because $g$ is linear (hence increasing, `cones_hom_image_chain`) and norm-decreasing (`cones_hom_image_ub1`); and a test evaluated at a `cone_sup_ball` is the *real* supremum of its values along the chain (`test_of_sup`, which reads the monotonicity `test_fun_le` and the $\omega$-continuity field `test_cont` of a test as one identity). Pushing the cone-sup through $g$ by $\omega$-continuity (`cones_hom_continuous`) and then applying `test_of_sup` gives `test_pullback_cont`, the test-side fact behind $\omega$-continuity of pre-/post-composition on the internal hom.

```coq
(* theories/icones/test_pullback.v — Section TestOfSup
   (C : MCone.type Ar, Z : ar_obj Ar, m : test_of Ar Z C) and
   Section TestPullbackCont
   (D1 D2 : MCone.type Ar, g : cones_hom D1 D2, m : test_of Ar Z D2) *)
Lemma test_of_sup.

Lemma cones_hom_image_chain.

Lemma cones_hom_image_ub1.

Lemma test_pullback_cont.
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

The construction climbs the three layers on $\Lambda:=(f\mapsto g\circ f\circ h)$, and each step is a named lemma. As a `cones_hom` (`linhom_map_cones`): linearity `linhom_map_linear`; norm-decrease `linhom_map_norm_le1`, from the chain $\lVert g(f(h\,x))\rVert\le\lVert f(h\,x)\rVert\le\lVert f\rVert\lVert x\rVert$ and the least-upper-bound property of the operator norm; and $\omega$-continuity `linhom_map_continuous`, which reduces by test-separation (Mssep) in $D_2$ to pushing a cone-sup through $g$, i.e. to `test_pullback_cont`. As an `mcones_hom` (`linhom_map_mcones`) the crux is measurable-path preservation *in $f$*, `linhom_map_pres_path`: for a measurable path $\Phi$ of $C_1\multimap D_1$ the bivariate $D_1$-path $\delta(s,r):=(\Phi\,r)(h(\gamma_2\,s))$ is measurable — obtained by testing $\Phi$ against the § 5.1 test of the path $h\circ\gamma_2$ — and pulling a $D_2$-test back along $g$ keeps it measurable by the bivariate `test_pullback_meas_bivar`. As an `icones_hom` (`linhom_map_icones`) what remains is integral preservation `linhom_map_pres_int`: $\Lambda(\int\Phi\,d\mu)=\int(\Lambda\circ\Phi)\,d\mu$, proved by uniqueness of the linhom path integral (`icone_integral_eqP` against `linhom_int_car_pettis`) plus $g$'s own integral preservation and the Pettis spec of $D_2$. The computation law `linhom_map_iconesE` records that the underlying map of the resulting morphism is `linhom_map_fun h g` on the nose.

> **Paper — Proposition 5.8, proof** (arXiv 2212.02371 / LMCS 21(1:1)). The linearity and continuity of $h\multimap g$ result from the same properties satisfied by $g$ and $h$. The fact that $\lVert h\multimap g\rVert\le 1$ results from the fact that $\lVert g\rVert,\lVert h\rVert\le 1$, so let us check that $h\multimap g$ is measurable. […] For $s\in Y$ and $r\in X$ we have $\varphi(s,r)=m(s,g(\eta_1(r)(h(\gamma(s)))))=m(s,g(\delta_1(s)(r)))=m(s,g(\mathsf{fl}(\delta_1)(s,r)))$ where $\delta_1=\mathsf{sw}^{-1}(\eta_1)\circ h\circ\gamma\in\mathsf{Path}(Y,\mathsf{Path}(X,D_1))$ by Lemma 5.3 and hence $g\circ\mathsf{fl}(\delta_1)\in\mathsf{Path}(Y\times X,D_2)$ by Lemma 3.19 so that $\varphi$ is measurable.

> **Difference.** The paper's measurability argument goes through $\mathsf{sw}^{-1}$ (Lem 5.3) and the flattening of Lem 3.19. The mechanisation reaches the same conclusion through the reusable *test-pullback* characterisation of Def 3.13 instead — `test_pullback_meas_bivar` for measurability and `test_pullback_cont` for continuity, both in `theories/icones/test_pullback.v` — which avoids inverting $\mathsf{sw}$ and is what makes `linhom_map_pres_path` a single application rather than a chain of transports. The bivariate shape of the pullback lemma exists precisely for this consumer: it folds the pair $(s,r)$ through `ar_prod` so that the § 5.3 expression $\varphi(s,r)=m(s,g(\delta(s,r)))$ type-checks at the product arity.

```coq
(* theories/homs/linhom_functor.v — Section LinhomMapHom *)
Lemma linhom_map_linear.
Lemma linhom_map_norm_le1.
Lemma linhom_map_continuous.
Definition linhom_map_cones.
Lemma linhom_map_pres_path.
Definition linhom_map_mcones.
Lemma linhom_map_pres_int.
Lemma linhom_map_iconesE.
```

### Prop 5.8 functoriality (`linhom_post_icones`, `linhom_pre_icones`, `linhom_map_icones_id`, `linhom_map_icones_comp`)

Prop 5.8 gives the action of $\multimap$ on a *pair* of morphisms; the development almost always uses one slot at a time. The covariant post-composition action $C\multimap g:=(\mathrm{id}_C)\multimap g$ is `linhom_post_icones`, with $(C\multimap g)(f)=g\circ f$ (`linhom_post_iconesE`); the contravariant pre-composition action $h\multimap D:=h\multimap(\mathrm{id}_D)$ is `linhom_pre_icones`, with $(h\multimap D)(f)=f\circ h$ (`linhom_pre_iconesE`). Post-composition is the load-bearing one: it is the witness of the naturality of the tensor–hom bijection in the codomain, and hence of paper Eq 5.1. Functoriality itself is two equations *in $\mathbf{ICones}$*: `linhom_map_icones_id` ($\mathrm{id}_C\multimap\mathrm{id}_D=\mathrm{id}_{C\multimap D}$) and `linhom_map_icones_comp` ($(h'\circ h)\multimap(g\circ g')=(h'\multimap g')\circ(h\multimap g)$, contravariant in the first slot). Both reduce by `icones_hom_eq` to the object-level laws `linhom_map_id` / `linhom_map_comp` of `linhom.v`, which in turn are `linhom_eq` plus the pointwise computation rule `linhom_map_funE` — the equation $(h\multimap g)(f)(x)=g(f(h\,x))$ that every $\multimap$-calculation rewrites with.

> **Paper — § 5.3** (arXiv 2212.02371 / LMCS 21(1:1), after the proof of Proposition 5.8). So we have defined a functor $\multimap:\mathbf{ICones}^{\mathrm{op}}\times\mathbf{ICones}\to\mathbf{ICones}$. We identify $1\multimap{-}$ with the identity functor: we make no distinction between $x\in C$ and the function $\widehat{x}\in 1\multimap C$ (this notation is introduced in the proof of Theorem 4.18).

> **Difference.** The paper asserts functoriality in that one sentence, and in the same breath *identifies* $1\multimap{-}$ with the identity functor, writing $\widehat{x}$ for $x$. The formalisation keeps the two types apart and mechanises the identification as an explicit isomorphism instead: `linhom_one_iso : icones_iso Ar (1 ⊸ C) C` in `theories/homs/tensor_iso.v`, built by `icones_iso_of_cancel` from evaluation at the unit (`eval1`) and the scaling lift (`lo_lift`), with the round-trips `linhom_one_fwdK` / `linhom_one_bwdK`. Note also which naturality is available: the one-sided actions give naturality of the tensor–hom bijection $\Phi$ in $D$ and in $B$, which is all § 5.4–5.5 consumes; naturality in the $C$ slot, which would be stated with `linhom_pre_icones`, is deliberately not developed — the symmetry coherence is derived instead from the pure-tensor law $\sigma(x\otimes y)=y\otimes x$.

```coq
(* theories/homs/linhom_functor.v — Section LinhomOneSided *)
Definition linhom_post_icones.
Definition linhom_pre_icones.
Lemma linhom_post_iconesE.
Lemma linhom_pre_iconesE.
```

```coq
(* theories/homs/linhom_functor.v — Section LinhomMapFunctor *)
Lemma linhom_map_icones_id.
Lemma linhom_map_icones_comp.
```

```coq
(* theories/homs/linhom.v — Section LinhomMap *)
Lemma linhom_map_funE.
Lemma linhom_map_id.
Lemma linhom_map_comp.
```

### ICones isos (`icones_iso`, `icones_isoP`, `icones_iso_of_cancel`, `icones_iso_refl`, `icones_iso_sym`, `icones_iso_trans`, `iso_fwd_bij`)

Every structural equivalence the paper states as "is an iso" — Thm 5.9's $k$, the currying iso of Thm 5.12, the associator, unitors and braiding of Thm 5.15, the Seely isos of § 9 — is carried in the formalisation by one record, `icones_iso Ar B C`: a forward morphism `iso_fwd`, a backward morphism `iso_bwd`, and the two round-trip *equations of morphisms* `iso_fwdK` and `iso_bwdK` stated with `icones_comp` and `icones_id`. Two smart constructors build it: `icones_isoP` from the two equations as given, and the Yoneda-style `icones_iso_of_cancel` from *pointwise* cancellation ($\forall x,\ \mathrm{bwd}(\mathrm{fwd}\,x)=x$ and dually), which it upgrades to the equational form through `icones_hom_eq`. The latter is what almost every client uses, because a concrete iso is normally proved by computing on points. The isos then form a groupoid — `icones_iso_refl` (the identity iso), `icones_iso_sym` (swap the two morphisms and the two round-trips) and `icones_iso_trans` (compose forwards, compose backwards in the other order) — and the underlying forward *function* is recovered as a bijection: `iso_can` / `iso_can'` are the two pointwise cancellations, `iso_fwd_inj` injectivity, `iso_fwd_bij` bijectivity with `iso_bwd` as the explicit two-sided inverse.

The same file also carries `mk_icones_hom`, the flat smart constructor for morphisms — a function plus its five obligations (linearity, $\omega$-continuity, the norm bound, path preservation, integral preservation) — with computation rule `mk_icones_homE`, which spares every client the three-level nesting `MkIConesHom (MkMConesHom (ConesHom …) …) …`.

> **Paper — Theorem 5.9, proof** (arXiv 2212.02371 / LMCS 21(1:1)). Let $(D_i)_{i\in I}$ be a family of measurable cones and let $D=\mathbin{\&}_{i\in I}D_i$ as described in the proof of Theorem 4.16. We have a morphism $k=\langle C\multimap\mathrm{pr}_i\rangle_{i\in I}\in\mathbf{ICones}\bigl(C\multimap D,\ \mathbin{\&}_{i\in I}(C\multimap D_i)\bigr)$ and we must prove that $k$ is an iso.

> **Difference.** The paper has no formal notion of "iso in $\mathbf{ICones}$" — it argues that a morphism is bijective and that the set-theoretic inverse is again a morphism, then calls the pair an iso. `icones_iso` makes that argument a datum, and deliberately states the round-trips as equations between *morphisms* rather than as pointwise cancellations: downstream coherence proofs (the pentagon, the triangle, the hexagon, the Seely squares) rewrite with them inside larger composites, where a pointwise statement would not apply. `icones_iso_of_cancel` is the bridge that lets a client still *prove* the iso pointwise. Note that no `icones_iso` is registered as a coercion to `icones_hom`: `iso_fwd φ` is always written explicitly, which is why that projection appears verbatim in so many § 5 and § 9 snippets.

```coq
(* theories/homs/icones_iso.v — Section IConesIso *)
Record icones_iso.
```

```coq
(* theories/homs/icones_iso.v — Section IConesIsoBuild *)
Definition icones_isoP.
Definition icones_iso_of_cancel.
```

```coq
(* theories/homs/icones_iso.v — Section IConesIsoCancel *)
Lemma iso_can.
Lemma iso_can'.
Lemma iso_fwd_inj.
Lemma iso_fwd_bij.
```

```coq
(* theories/homs/icones_iso.v — Section IConesIsoGroupoid *)
Definition icones_iso_refl.
Definition icones_iso_sym.
Definition icones_iso_trans.
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

### Lem 5.10 (`lfun_path_swap`)

Swapping the two hom-arguments across a path: from $f\in\mathbf{ICones}(B,\mathrm{Path}(X,C\multimap D))$ one obtains $f'=\lambda(y,r,x).\,f(x,r,y)\in\mathbf{ICones}(C,\mathrm{Path}(X,B\multimap D))$. This is the key ingredient of the tensor–hom iso (used by `path_tens_to_X`).

> **Paper — Lemma 5.10** (arXiv 2212.02371, `lemma:lfun-path-swap`). Let $X\in\mathbf{AR}$ and let $B,C,D$ be measurable cones. Let $f$ be an element of $\mathbf{ICones}(B,\mathrm{Path}(X,C\multimap D))$. Then $f'=\lambda(y,r,x).\,f(x,r,y)$ belongs to $\mathbf{ICones}(C,\mathrm{Path}(X,B\multimap D))$.

```coq
(* theories/homs/tensor_iso.v — Section LfunPathSwap,
   Variables (R : realType) (Ar : MeasSubcat R), (X : ar_obj Ar),
   (B C D : ICone.type Ar),
   f : icones_hom Ar B (path_car Ar X (linhom_car Ar C D)),
   Local Notation PBD := (path_car Ar X (linhom_car Ar B D)) *)
Definition lfun_path_swap : icones_hom Ar C PBD :=
  mk_icones_hom lfps lfps_linear lfps_continuous lfps_norm_le
    (fun W δ Hδ => lfps_pres_path (W:=W) (δ:=δ) Hδ) lfps_pres_int.

Lemma lfun_path_swapE (y : C) (r : ar_carrier Ar X) (x : B) :
  linhom_fun (path_fun (lfun_path_swap y) r) x =
  linhom_fun (path_fun (f x) r) y.
```

### Lem 5.11 (`path_tens_to_X`, `path_tens_to_X_unit`)

> **Where the code lives.** `theories/homs/tensor_iso.v` (Sections `PathTensToX` / `PathTensToXGen`). The mechanisation proves the lemma directly at an arbitrary integrable codomain $D$; the paper's scalar-codomain statement is the $D := 1$ instance. (An earlier scalar-only copy was verbatim-superseded by this general version and has been removed.)

A candidate path $\eta:X\to(B\otimes C)\multimap 1$ is genuinely a measurable path as soon as it is bounded and its pure-tensor evaluations are jointly measurable. This is the key observation behind the measurability of the tensor–hom iso $\Psi$ (Thm 5.12).

> **Paper — Lemma 5.11** (arXiv 2212.02371, `lemma:path-tens-to-one`). Let $X\in\mathbf{AR}$ and $B,C$ be integrable cones. Let $\eta:X\to\underline{(B\otimes C)\multimap 1}$ be a function. One has $\eta\in\underline{\mathrm{Path}(X,(B\otimes C)\multimap 1)}$ as soon as (i) $\eta(X)\subseteq\underline{(B\otimes C)\multimap 1}$ is bounded, and (ii) for all $Y\in\mathbf{AR}$, $\beta\in\underline{\mathrm{Path}(Y,B)}$ and $\gamma\in\underline{\mathrm{Path}(Y,C)}$, the function $\lambda(s,r)\in Y\times X.\ \eta(r)(\beta(s)\otimes\gamma(s)):Y\times X\to\mathbb{R}_{\geq 0}$ is measurable.

> **Difference.** The two hypotheses `ηbound` ($\eta$ is bounded) and `ηpt` (the pure-tensor evaluation $\lambda s.\,\eta(\varphi\,s)(\beta\,s\otimes\gamma\,s)$ is measurable) match the paper's two bullet conditions. The mechanisation factors the norm-$\le 1$ case as `path_tens_to_X_unit`; the general bounded case (`path_tens_to_X`) rescales $\eta$ into the unit ball and applies it. It is stated at an arbitrary integrable codomain $D$ — strictly more general than the paper's $1$.

```coq
(* theories/homs/tensor_iso.v — Section PathTensToXGen *)
Lemma path_tens_to_X : is_measurable_path η.

(* norm-≤1 case (Section PathTensToX) *)
Lemma path_tens_to_X_unit : is_measurable_path η.
```

### § 5.4 tau (`tau`, `ptensor`, `ptensorE`)

The paper's tensor $B\otimes C$ is produced by the adjoint functor theorem, so it comes with no explicit carrier (Rem 5.1 — the formalization does build one, see *Beyond the paper*); everything one can *compute* with it therefore comes from a single element. Transporting the identity $\mathrm{Id}_{B\otimes C}$ across the adjunction bijection $\Phi$ yields the universal map $\tau_{B,C}\in\mathbf{ICones}(B,C\multimap B\otimes C)$, and the **pure tensor** is its double application, $x\otimes y=\tau_{B,C}(x)(y)$. This is the meaning of the infix `⊗p` that appears in the Rocq snippets of Thm 5.13, Prop 5.14, § 9 and *Beyond the paper*.

> **Paper — § 5.4** (arXiv 2212.02371, LMCS 21(1:1), p. 1:46). We define $$\tau_{B,C}=\Phi_{B,C,B\otimes C}(\mathrm{Id}_{B\otimes C})\in\mathbf{ICones}(B,C\multimap B\otimes C)=\mathcal{B}(B,C\multimap B\otimes C)$$ and, for $x\in B$ and $y\in C$ we use the notation $x\otimes y=\tau_{B,C}(x,y)$.

> **Difference.** The paper writes the pure tensor as $\tau_{B,C}(x,y)$: by Def 5.6 the iterated hom $B\multimap(C\multimap B\otimes C)$ *is* the cone $(B,C\multimap B\otimes C)$ of integrable bilinear maps, and $\mathbf{ICones}(B,C\multimap B\otimes C)$ is its unit ball $\mathcal{B}$ — so $\tau$ may be applied to two arguments at once. The mechanisation keeps the curried form, `ptensor x y = linhom_fun (tau B C x) y`, with `ptensorE` as the (definitional) computation law; the bilinear reading is recovered through `bilin_data` (Def 5.6) where it is needed.

`theories/homs/tensor.v` is the § 5.4 re-export layer: it `Export`s the three construction modules and then re-declares `tau` and `ptensor` *after* them, deliberately shadowing the homonymous `ptensor` of `tensor_hom_iso.v`. The `tau`/`ptensor` of `tensor.v` are the ones every downstream file and every snippet in this document uses; `⊗p` is that file's `Local Notation`, reused verbatim in `smcc.v`.

```coq
(* theories/homs/tensor.v — Section Tensor,
   Variables (R : realType) (Ar : MeasSubcat R),
   Local Notation "C ⊸ D" := (linhom_car Ar C D),
   Local Notation "B ⊗ C" := (tensor Ar B C),
   Local Notation "x ⊗p y" := (ptensor x y) *)
Definition tau.

Definition ptensor.

Lemma ptensorE.
```

### Eq 5.1 (`tensor_curry_factor`, `tensor_curryE`)

Equation (5.1) is the computation rule of the whole tensor layer: the adjunction bijection $\Phi=\,$`tensor_curry` is completely determined by $\tau$, so evaluating a curried morphism on a pure tensor just applies the original morphism. Every extensionality result (Prop 5.14) and every coherence diagram of § 5.5 is proved by rewriting with it.

> **Paper — § 5.4, Equation (5.1)** (arXiv 2212.02371, LMCS 21(1:1), p. 1:46). By naturality of $\Phi$ we have that, for each $f\in B\otimes C\multimap D$, $$\Phi_{B,C,D}(f)=f\circ\tau_{B,C}.\qquad(5.1)$$

> **Difference.** Read literally, $f\circ\tau_{B,C}$ does not typecheck: $\tau_{B,C}(x)$ lives in $C\multimap B\otimes C$ while $f$ maps out of $B\otimes C$. `tensor_curry_factor` makes the intended hom-functor action explicit — $\Phi(f)=(C\multimap f)\circ\tau_{B,C}$, i.e. `icones_comp (linhom_post_icones f) (tau B C)`, post-composition by $f$ *inside* the hom (the covariant half of Prop 5.8). It is derived from the concrete naturality `tensor_curry_natural_post` at $h:=f$ and $f_0:=\mathrm{Id}_{B\otimes C}$; evaluating the action through `linhom_map_funE` gives the pointwise form `tensor_curryE`, $\Phi(f)(x)(y)=f(x\otimes y)$.

> **Difference (scope of naturality).** The construction supplies naturality of $\Phi$ in $D$ — existentially as `tensor_curry_natural_D` and concretely as `tensor_curry_natural_post`, whose witness is the explicit action $C\multimap h$ — and naturality in $B$ (`tensor_curry_natural_B`, witnessed by the uncurried $\tau\circ u$). Naturality in the $C$ slot is deliberately **not** developed: it would require a naturality square for the contravariant action of $\multimap$ in its left argument (`linhom_pre_icones`), and the one place it could serve — the symmetry coherence — is instead settled by the pure-tensor law $\gamma(x\otimes y)=y\otimes x$ (Eq 5.4). Together with the two round-trips `tensor_curryK` and `tensor_uncurryK`, this is the complete set of adjunction primitives the § 5.4–§ 5.5 development consumes.

```coq
(* theories/homs/tensor.v — Section Tensor *)
Lemma tensor_curry_factor.

Lemma tensor_curryE.
```

```coq
(* theories/homs/tensor_construct.v — Section TensorCurry (naturality in D)
   and Section TensorNaturalB (naturality in B) *)
Lemma tensor_curry_natural_post.

Lemma tensor_curry_natural_D.

Lemma tensor_curry_natural_B.
```

### § 5.4 bifunctor (`tensor_mor`, `tensor_mor_id`, `tensor_morE`)

$\otimes$ is not merely an operation on objects: it acts on morphisms, sending $f:B_1\to B_2$ and $g:C_1\to C_2$ to $f\otimes g:B_1\otimes C_1\to B_2\otimes C_2$. Concretely $f\otimes g$ is the uncurrying of $\tau_{B_2,C_2}\circ f$ precomposed in the hom slot by $g$, and it computes on pure tensors exactly as one expects: $(f\otimes g)(x\otimes y)=(f\,x)\otimes(g\,y)$.

> **Paper — § 5.4** (arXiv 2212.02371, LMCS 21(1:1), p. 1:45). Let $C$ be an integrable cone. We denote by $-\otimes C$ the left adjoint of the functor $C\multimap-$, see Theorem 5.9. Because $\multimap$ is a functor $\mathbf{ICones}^{\mathrm{op}}\times\mathbf{ICones}\to\mathbf{ICones}$ (see Section 5.3), we know by the adjunction with a parameter theorem ([Mac71], Chapter IV, Section 7, Theorem 3), that the so defined operation $\otimes$ can uniquely be extended in a bifunctor $\otimes:\mathbf{ICones}^2\to\mathbf{ICones}$ in such a way that the bijection $\Phi_{B,C,D}:\mathbf{ICones}(B\otimes C,D)\to\mathbf{ICones}(B,C\multimap D)$ given by the adjunction for each $C$ is natural in $B$, $C$, $D$.

> **Difference.** The paper obtains the morphism action abstractly, from the uniqueness clause of Mac Lane's adjunction-with-a-parameter theorem. The formalization instead *defines* it (`tensor_mor`) and proves the bifunctor laws directly, because the § 5.5 coherence proofs need a computation rule rather than a uniqueness statement: the identity law `tensor_mor_id` (precomposition by $\mathrm{id}_C$ collapses through `linhom_map_icones_id`, leaving the round-trip `tensor_curryK`), the pure-tensor law `tensor_morE` (from `tensor_uncurryK` and Eq 5.1), and the composition law $(f_2\circ f_1)\otimes(g_2\circ g_1)=(f_2\otimes g_2)\circ(f_1\otimes g_1)$, proved as `tensor_mor_comp` in `theories/cbv/em_cartesian.v` — where it is first needed, for the Eilenberg–Moore cartesian structure. The SMCC bundle of Thm 5.15 records only the identity law (`smcc_mor_id`), since that is all its coherence witnesses use.

```coq
(* theories/homs/tensor.v — Section Tensor *)
Definition tensor_mor.

Lemma tensor_mor_id.
```

```coq
(* theories/homs/smcc.v — Section SMCC *)
Lemma tensor_morE.
```

```coq
(* theories/cbv/em_cartesian.v — the composition law, proved downstream *)
Lemma tensor_mor_comp.
```

### § 5.4 bilinearity (`ptensorZl`, `ptensorZr`, `linhom_funZ`)

The pure tensor is bilinear, so a non-negative scalar may be moved through either slot: $(r\cdot x)\otimes y=r\cdot(x\otimes y)=x\otimes(r\cdot y)$. Linearity in $y$ is just linearity of the linear morphism $\tau(x)$; linearity in $x$ uses that $\tau$ is *itself* a morphism of cones, so it scales $\tau(x)$ pointwise — which is what `linhom_funZ` records. Both are hypotheses of the triangle coherence (§ 5.5), where the two sides reach $u\cdot(x\otimes y)$ through opposite slots.

> **Paper — § 5.4** (arXiv 2212.02371, LMCS 21(1:1), p. 1:46). $\tau_{B,C}=\Phi_{B,C,B\otimes C}(\mathrm{Id}_{B\otimes C})\in\mathbf{ICones}(B,C\multimap B\otimes C)=\mathcal{B}(B,C\multimap B\otimes C)$.

> **Difference.** The paper states bilinearity of $\otimes$ only through this typing: by Def 5.6, $(B,C\multimap B\otimes C)$ *is* the cone of integrable bilinear continuous maps, so "$\tau$ is a morphism" already says "$x\otimes y$ is bilinear". The formalization instead names the individual laws it rewrites with, where they are first needed: the two scaling laws `ptensorZl` / `ptensorZr` in `theories/homs/smcc.v` (hypotheses of the triangle coherence), and the right-slot additivity $x\otimes(y+z)=x\otimes y+x\otimes z$ as `ptensorDr` in `theories/programs/infra/cbv_anchors.v`, where the boolean-basis expansion of the PPL layer needs it. All three come straight from linearity of the linhom $\tau(x)$, or of $\tau$ itself.

```coq
(* theories/homs/smcc.v — Section SMCC *)
Lemma linhom_funZ.

Lemma ptensorZr.

Lemma ptensorZl.
```

```coq
(* theories/programs/infra/cbv_anchors.v — the additivity half, proved downstream *)
Lemma ptensorDr.
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

The iso is also used at the element level, so `theories/homs/tensor.v` names its two directions — `tensor_hom_fwd` and `tensor_hom_bwd` — and records that the forward map is bijective (`tensor_hom_fwd_bij`, from `iso_fwd_bij`). At the *morphism* level the corresponding fact is that $\Phi=\,$`tensor_curry` is injective, because `tensor_uncurry` is a left inverse (`tensor_curryK`): this is `tensor_curry_inj`, and it is the engine of the extensionality principle of Prop 5.14 — two morphisms out of $B\otimes C$ agreeing on pure tensors have equal curryings by Eq 5.1, hence are equal.

```coq
(* theories/homs/tensor.v — Section Tensor *)
Definition tensor_hom_fwd.

Definition tensor_hom_bwd.

Lemma tensor_hom_fwd_bij.

Lemma tensor_curry_inj.
```

### Thm 5.13 (`tensor_norm_le`, `tensor_normME`)

The norm of a pure tensor $x\otimes y$ is exactly the product of the two norms $\lVert x\rVert\,\lVert y\rVert$.

> **Paper — Theorem 5.13** (arXiv 2212.02371). For each $x\in\underline{B}$ and $y\in\underline{C}$ we have $\lVert x\otimes y\rVert=\lVert x\rVert\,\lVert y\rVert$.

> **Difference.** The paper states the equality directly; the formalization splits it into `tensor_norm_le` (the $\le$ direction, from $\tau_{B,C}\in\mathbf{ICones}(B,C\multimap(B\otimes C))$) and `tensor_normME` (the full equality). *Why:* the $\ge$ direction relies on the dual-norm characterisation of Prop 3.11, so it is factored out as a separate step. The equality is proved once in `theories/homs/tensor_hom_iso.v` as `tensor_normM`, stated at the *uncurried* reading of the pure tensor — `linhom_fun (tensor_curry (icones_id …) x) y`, i.e. before the `⊗p` notation is available — and `tensor_normME` in `tensor.v` is that result in the notation the rest of §5 uses. The two are the same theorem; `tensor_normM` is where the `le_anti` split between `ptensor_norm_le` and `ptensor_norm_ge` actually happens.

```coq
(* theories/homs/tensor_hom_iso.v — Section NormM *)
(* Paper Thm 5.13 (full), at the uncurried reading of x ⊗ y. *)
Lemma tensor_normM (x : B) (y : C) :
  cone_norm (linhom_fun (tensor_curry (icones_id Ar (tensor B C)) x) y)
  = cone_norm x * cone_norm y.

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

### Eqs 5.2–5.4 (`tensor_assoc`, `tensor_lunit`, `tensor_runit`, `tensor_braid`, `tensor_assocEp`, `tensor_lunitEp`, `tensor_runitEp`, `tensor_braidEp`)

The associator $\alpha$, the two unitors $\lambda$ and $\rho$, and the braiding $\gamma$ are the structural isos of the monoidal structure. Existence is Yoneda-style — each is the transport of an identity across a composite of adjunction bijections — but what the coherence proofs consume is not existence: it is the *pure-tensor computation law* each one satisfies. Without those laws the isos are opaque data; with them, every diagram of § 5.5 reduces to an equation between pure tensors.

> **Paper — § 5.5, Equations (5.2)–(5.4)** (arXiv 2212.02371, LMCS 21(1:1), pp. 1:49–1:50). Moreover the definition of the natural iso $\Phi$ implies that for all $x_1\in B_1$, $x_2\in B_2$ and $x_3\in B_3$, one has $$\alpha_{B_1,B_2,B_3}((x_1\otimes x_2)\otimes x_3)=x_1\otimes(x_2\otimes x_3)\qquad(5.2)$$ Similarly one defines natural isos $\lambda_B\in\mathbf{ICones}(1\otimes B,B)$ (using the obvious natural bijection $\mathbf{ICones}(1,B\multimap C)\to\mathbf{ICones}(B,C)$), $\rho_B\in\mathbf{ICones}(B\otimes 1,C)$ (using the obvious natural iso $(1\multimap C)\to C$ in $\mathbf{ICones}$) and $\gamma_{B_1,B_2}\in\mathbf{ICones}(B_1\otimes B_2,B_2\otimes B_1)$ (using the natural iso of Lemma 5.5). These isos satisfy the following equations $$\forall x\in B,\ \forall u\in\mathbb{R}_{\geq 0}\quad \lambda_B(u\otimes x)=ux=\rho_B(x\otimes u)\qquad(5.3)$$ $$\forall x_1\in B_1,\ \forall x_2\in B_2\quad \gamma_{B_1,B_2}(x_1\otimes x_2)=x_2\otimes x_1.\qquad(5.4)$$

> **Difference.** Three naming/packaging points. (i) The paper's braiding is $\gamma$; the formalization calls it `tensor_braid` (built, as the paper says, from the argument-swap iso of Lem 5.5). (ii) The four names in `theories/homs/smcc.v` are re-exports under the paper's names of the proved isos of `theories/homs/tensor_iso.v` (`tensor_assoc_iso`, `tensor_lunit_iso`, `tensor_runit_iso`, `tensor_braid_iso`), and the `…Ep` laws restate that file's computation laws (`tensor_assocE`, `tensor_lunitE`, `tensor_runitE`, `tensor_braidE`) in terms of the § 5.4 pure tensor `ptensor`. (iii) The unit $1$ is `cone_one_car Ar` ($\mathbb{R}_{\geq 0}$), so Eq (5.3)'s scalar action $ux$ is mechanised as `precone_scale (c1_val u) x`; the codomain of $\rho$ is $A$ (the paper's displayed $C$ in "$\rho_B\in\mathbf{ICones}(B\otimes 1,C)$" is a slip, corrected by its own Eq (5.3)).

```coq
(* theories/homs/smcc.v — Section SMCC,
   Local Notation "B ⊗ C" := (tensor Ar B C),
   Local Notation "x ⊗p y" := (ptensor x y),
   Local Notation "one" := (cone_one_car Ar) *)
Definition tensor_assoc.

Definition tensor_lunit.

Definition tensor_runit.

Definition tensor_braid.

Lemma tensor_assocEp.

Lemma tensor_lunitEp.

Lemma tensor_runitEp.

Lemma tensor_braidEp.
```

```coq
(* theories/homs/tensor_iso.v — the proved isos and computation laws behind them *)
Definition tensor_assoc_iso.

Lemma tensor_assocE.

Definition tensor_lunit_iso.

Lemma tensor_lunitE.

Definition tensor_runit_iso.

Lemma tensor_runitE.

Definition tensor_braid_iso.

Lemma tensor_braidE.
```

### § 5.5 coherence (`tensor_braid_invol`, `tensor_triangle`, `tensor_pentagon`, `tensor_hexagon`)

The monoidal coherence of Thm 5.15 is **proved**, not assumed: each diagram is checked by evaluating both composites on (iterated) pure tensors and reading off Eqs 5.2–5.4. This is exactly the route the paper prescribes, and it is why Prop 5.14 is stated at all. The four witnesses are separate top-level lemmas, so each square can be audited on its own — `Print Assumptions tensor_pentagon` is a meaningful question with an answer.

> **Paper — § 5.5** (arXiv 2212.02371, LMCS 21(1:1), p. 1:50). The required coherence diagrams are easily proven using Equations (5.2), (5.3) and (5.4) combined with Proposition 5.14. In that way, we have endowed $\mathbf{ICones}$ with an SMC structure whose monoidal product is our tensor product $\otimes$. The natural isomorphism $\Phi$ tells us moreover that this SMC is closed.

> **Difference.** The paper's "easily proven" is discharged at four specific trees, which is all Thm 5.15 needs: the symmetry law $\gamma_{B,A}\circ\gamma_{A,B}=\mathrm{id}$ by the binary `tensor_ext` and Eq 5.4; the triangle by the ternary `tensor_ext3`, both sides reaching $u\cdot(x\otimes y)$ on $(x\otimes u)\otimes y$ — the left through Eqs 5.2/5.3 and `ptensorZr`, the right through Eq 5.3 and `ptensorZl`; the pentagon by the quaternary `tensor_ext4`, both composites reaching $w\otimes(x\otimes(y\otimes z))$ by repeated `tensor_assocEp` and `tensor_morE`; and the hexagon by `tensor_ext3`, both composites reaching $y\otimes(z\otimes x)$. These four lemmas are the witnesses that populate the elided `smcc_braid_invol` / `smcc_triangle` / `smcc_pentagon` / `smcc_hexagon` fields of the `ICones_smcc` instance shown under Thm 5.15.

```coq
(* theories/homs/smcc.v — Section SMCC *)
Lemma tensor_braid_invol.

Lemma tensor_triangle.

Lemma tensor_pentagon.

Lemma tensor_hexagon.
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
| §6.1 δ | The Dirac mass $\boldsymbol\delta^{X}(r)\in\mathsf{FMeas}(X)$, its unit total mass, and the Dirac path $\boldsymbol\delta^{X}\in\mathsf{Path}(X,\mathsf{FMeas}(X))$ — the identity of $\mathbf{Skern}$ and the inverse map of Thm 6.1. | `dirac_fmeas`, `dirac_fmeas_E`, `dirac_fmeas_norm`, `dirac_path` — `theories/homs/bilin.v`; `dirac_path_norm_le1` — `theories/kernels/skern.v` |
| Cat 6 | The category $\mathbf{Skern}$ of substochastic kernels: objects in $\mathbf{Ar}$, morphisms $\kappa : X \leadsto \mathsf{FMeas}(Y)$. Given unbundled — there is no single `Skern` declaration; the category is the hom record plus its identity, composition and the three category laws. | `Skern_hom`, `Skern_id`, `Skern_comp`, `Skern_compIl`, `Skern_compIr`, `Skern_compA` — `theories/kernels/skern.v` |
| Cat 6 laws | Equality of kernels is equality of the underlying paths, and Kleisli composition satisfies the two identity laws and associativity. | `Skern_hom_eq`, `Skern_compIl`, `Skern_compIr`, `Skern_compA` — `theories/kernels/skern.v` |
| Thm 6.1 | Bijection $\mathsf{Path}(X, B) \simeq \mathsf{FMeas}(X) \multimap B$ (cone iso) given by the integration map $\mathcal{I}^{B}_X$. | `int_to_linhom`, `int_to_linhom_iso` — `theories/homs/bilin.v` |
| Thm 6.1 forward | The five defining fields of $\mathcal{I}^{B}_X(\beta) : \mathsf{FMeas}(X)\multimap B$: linearity and $\omega$-continuity in $\mu$, operator-norm boundedness, measurable-path preservation and integral preservation. | `int_to_linhom_fun_linear`, `int_to_linhom_fun_continuous`, `int_to_linhom_fun_bounded`, `int_to_linhom_fun_pres_path`, `int_to_linhom_fun_pres_int`, `icone_integral_kernel_tonelli` — `theories/homs/bilin.v` |
| Thm 6.1 inverse | The inverse map $\mathcal{K}^{B}_X(f)=f\circ\boldsymbol\delta^{X}$, i.e. $r\mapsto f(\boldsymbol\delta^{X}(r))$, as a bounded measurable path. | `linhom_to_int`, `linhom_to_int_E` — `theories/homs/bilin.v` |
| Thm 6.1 round-trips | $\mathcal{K}\circ\mathcal{I}=\mathrm{id}$ on paths and $\mathcal{I}\circ\mathcal{K}=\mathrm{id}$ on linear maps, with the Dirac evaluation $\mathcal{I}(\beta)(\boldsymbol\delta^{X}(r))=\beta(r)$ and the Dirac approximation $\mu=\int_X\boldsymbol\delta^{X}\,d\mu$. | `K_I_int_to_linhom_path_E`, `I_K_int_to_linhom_E`, `int_to_linhom_fun_dirac`, `icone_integral_dirac_path` — `theories/homs/bilin.v` |
| Thm 6.2 | *Dirac density*: two $\mathbf{ICones}$ morphisms $\mathsf{FMeas}(X) \to B$ that agree on every Dirac mass $\boldsymbol\delta^{X}(r)$ are equal. | `dirac_dense` — `theories/exp/coalgebra.v` |
| Thm 6.5 | The functor $\mathsf{Klin} : \mathbf{Skern} \to \mathbf{ICones}$, sending $X \mapsto \mathsf{FMeas}(X)$ and a kernel to its integration map, is **fully faithful**. | `Skern_to_ICones_fully_faithful` (= the *regression anchor*) — `theories/kernels/kernel_embedding.v` |
| Thm 6.5 Klin | $\mathsf{Klin}$ is a functor: it sends $X$ to $\mathsf{FMeas}(X)$ and $\kappa$ to $\mathcal{I}^{\mathsf{FMeas}(Y)}_X(\kappa)$, preserving identities and composition. | `Skern_to_ICones_obj`, `Skern_to_ICones_mor_E`, `Skern_to_ICones_mor_norm_le1`, `Skern_to_ICones_mor_id`, `Skern_to_ICones_mor_comp` — `theories/kernels/kernel_embedding.v` |
| Thm 6.5 faithful / full | The two halves of the embedding, each a corollary of one round-trip: faithfulness from $\mathcal{K}\circ\mathcal{I}=\mathrm{id}$, fullness from $\mathcal{I}\circ\mathcal{K}=\mathrm{id}$. | `Skern_to_ICones_faithful`, `Skern_to_ICones_full`, `Skern_to_ICones_mor_to_skern` (with the section-local helpers `icones_to_linhom`, `icones_to_skern_norm_le1`) — `theories/kernels/kernel_embedding.v` |

`Skern_to_ICones_fully_faithful` is the lemma checked by `./verify.sh` and is
load-bearing for the whole development's axiom budget. It depends only on the
3 classical `boolp` axioms.

### §6.1 δ (`dirac_fmeas`, `dirac_fmeas_E`, `dirac_fmeas_norm`, `dirac_path`)

For $X\in\mathbf{Ar}$ and $r\in X$, the *Dirac mass* $\boldsymbol\delta^{X}(r)$ is the finite measure with $\boldsymbol\delta^{X}(r)(U)=1$ when $r\in U$ and $0$ otherwise. `dirac_fmeas` packages it as an element of $\mathsf{FMeas}(X)$: its underlying $\overline{\mathbb{R}}$-valued set function agrees with mathcomp-analysis's $\backslash\mathsf{d}_r$ on measurable sets (`dirac_fmeas_E`) and is the canonical extension off the $\sigma$-algebra, so it satisfies the `fmeas` canonicity invariant on the nose. Its total mass is exactly $1$ (`dirac_fmeas_norm`), and $r\mapsto\boldsymbol\delta^{X}(r)$ is a bounded measurable path `dirac_path` $\in\mathsf{Path}(X,\mathsf{FMeas}(X))$ — boundedness is immediate from the norm, and test-measurability against the canonical family $e_U:\mu\mapsto\mu(U)$ reduces to measurability of $r\mapsto\mathbf{1}_U(r)$. Being of unit norm, `dirac_path` is a substochastic kernel (`dirac_path_norm_le1`), which is why $\boldsymbol\delta^{X}$ is simultaneously the identity of $\mathbf{Skern}$ (Cat 6), the inverse map of Thm 6.1, and the density engine of Thm 6.2.

> **Paper — §6.1** (arXiv 2212.02371, `content.tex:4574`). The identity at $X$ is $\boldsymbol\delta^{X}\in\mathbf{Skern}(X,X)$.

```coq
(* theories/homs/bilin.v — Section DiracPath, Variables R Ar X *)

Definition dirac_fmeas.

Lemma dirac_fmeas_E.

Lemma dirac_fmeas_norm.

Definition dirac_path.
```

```coq
(* theories/kernels/skern.v — Section SkernId, Variables R Ar X *)
Lemma dirac_path_norm_le1.
```

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

### Cat 6 laws (`Skern_hom_eq`, `Skern_compIl`, `Skern_compIr`, `Skern_compA`)

$\mathbf{Skern}$ really is a category, and the proofs are exactly the two round-trips of Thm 6.1 read at a point. Equality of kernels reduces to equality of the underlying paths (`Skern_hom_eq`, by proof-irrelevance on the norm-bound field), and path extensionality (`path_eq`) reduces that in turn to a pointwise identity — which is how all three laws below are proved. The left identity $\boldsymbol\delta^{Y}\lambda=\lambda$ (`Skern_compIl`, post-composing $\lambda:X\leadsto Y$ with the identity at its target) is the Dirac approximation $\mu=\int_Y\boldsymbol\delta^{Y}\,d\mu$ applied at $\mu=\lambda(r)$; the right identity $\lambda\,\boldsymbol\delta^{X}=\lambda$ (`Skern_compIr`, pre-composing with the identity at the source) is the Dirac evaluation `int_to_linhom_fun_dirac`; and associativity (`Skern_compA`) is the integral-preservation field `int_to_linhom_fun_pres_int` of $\mathcal{I}^{\mathsf{FMeas}}$.

> **Paper — §6.1 "The category of substochastic kernels as a full subcategory of $\mathbf{ICones}$"** (arXiv 2212.02371, `content.tex:4574`). Then $\mathbf{Skern}$ is the category whose objects are those of $\mathbf{Ar}$ and: the identity at $X$ is $\boldsymbol\delta^{X}\in\mathbf{Skern}(X,X)$; and given $\kappa_1\in\mathbf{Skern}(X_1,X_2)$ and $\kappa_2\in\mathbf{Skern}(X_2,X_3)$, their composite $\kappa=\kappa_2\,\kappa_1$ is given by $\kappa(r_1)=\mathcal{I}^{\mathsf{FMeas}(X_3)}_{X_2}(\kappa_2)(\kappa_1(r_1))$.

> **Difference.** The paper's $\mathsf{FMeas}(Y)$ is used as-is; the formalization deliberately does *not* use mathcomp-analysis's `{finite_measure}` type for kernel codomains but the project's own `fmeas` record. *Why:* `fmeas R Y` already carries the whole `Precone → Cone → MCone → ICone` tower built in §§ 2–4, so $\mathsf{FMeas}(Y)$ is an object of $\mathbf{ICones}$ on the nose and all of Thm 6.1 applies without coercions; the canonicity invariant of `fmeas` (the underlying $\overline{\mathbb{R}}$-valued additive function is canonically extended off the $\sigma$-algebra) is what makes that equality definitional rather than up to isomorphism.

```coq
(* theories/kernels/skern.v — Section SkernLaws, Variables R Ar *)

Lemma Skern_hom_eq.

Lemma Skern_compIl.

Lemma Skern_compIr.

Lemma Skern_compA.
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

### Thm 6.1 forward (`int_to_linhom_fun_linear`, `int_to_linhom_fun_continuous`, `int_to_linhom_fun_bounded`, `int_to_linhom_fun_pres_path`, `int_to_linhom_fun_pres_int`, `icone_integral_kernel_tonelli`)

The forward map $\mathcal{I}^{B}_X(\beta):\mu\mapsto\int_X\beta(r)\,\mu(dr)$ is a *linear hom* — an element of $\mathsf{FMeas}(X)\multimap B$ — because of five separately proved fields, each one an instance of a § 4 result: linearity in $\mu$ (`int_to_linhom_fun_linear`, from the bilinearity half of Lem 4.7); $\omega$-continuity in $\mu$ (`int_to_linhom_fun_continuous`, from the $\omega$-continuity half of Lem 4.7, applied after rescaling $\beta$ into the unit ball by $(\lVert\beta\rVert_{\mathsf{Path}}+1)^{-1}$ and rescaling back); operator-norm boundedness with constant $\lVert\beta\rVert_{\mathsf{Path}}$ (`int_to_linhom_fun_bounded`, from Lem 4.2); measurable-path preservation in the $\mathsf{FMeas}$ argument (`int_to_linhom_fun_pres_path`, from the joint-measurability half of Lem 4.7, which in turn rests on Lem 4.6); and integral preservation (`int_to_linhom_fun_pres_int`), which goes through the scalar identity `icone_integral_kernel_tonelli` — a measurable path of finite measures is repackaged as a finite kernel and mathcomp-analysis's `integral_kcomp` swaps the two integration orders.

> **Paper — Theorem 6.1** (arXiv 2212.02371, `th:meas-path-equiv`). For each $X\in\mathbf{Ar}$ and integrable cone $B$, one has $\mathcal{I}^{B}_X\in\mathbf{ICones}(\mathsf{Path}(X,B),\mathsf{FMeas}(X)\multimap B)$ and $\mathcal{I}^{B}_X$ is an isomorphism which is natural in $X$ and in $B$.

> **Difference.** The paper asserts membership in $\mathsf{FMeas}(X)\multimap B$ in one breath; the mechanisation exhibits the `linhom_car` field by field, and each field is discharged from the § 4 lemma that carries it. *Why:* the fields are consumed separately downstream — `int_to_linhom_fun_pres_path` alone is what makes Kleisli composition in $\mathbf{Skern}$ well defined (Cat 6), and `int_to_linhom_fun_pres_int` alone is what makes it associative.

```coq
(* theories/homs/bilin.v — Section IntToLinhomFun,
   Variables (R : realType) (Ar : MeasSubcat R) (X : ar_obj Ar)
             (B : ICone.type Ar) (β : path_car Ar X B) *)

Lemma int_to_linhom_fun_linear.

Lemma int_to_linhom_fun_continuous.

Lemma int_to_linhom_fun_bounded.

Lemma int_to_linhom_fun_pres_path.

Lemma icone_integral_kernel_tonelli.

Lemma int_to_linhom_fun_pres_int.
```

### Thm 6.1 inverse (`linhom_to_int`, `linhom_to_int_E`)

The inverse of $\mathcal{I}^{B}_X$ is precomposition with the Dirac path: $\mathcal{K}^{B}_X(f)=f\circ\boldsymbol\delta^{X}$, i.e. $\mathcal{K}^{B}_X(f)(r)=f(\boldsymbol\delta^{X}(r))$ (`linhom_to_int_E`). It lands in $\mathsf{Path}(X,B)$ for two reasons, both read off the `linhom_car` structure of $f$: the values are uniformly bounded because $f$ has an operator norm and $\lVert\boldsymbol\delta^{X}(r)\rVert=1$, and the composite is test-measurable because $f$ preserves measurable paths and $\boldsymbol\delta^{X}$ is one.

> **Paper — Theorem 6.1** (arXiv 2212.02371, `th:meas-path-equiv`). $\mathcal{I}^{B}_X$ is an isomorphism which is natural in $X$ and in $B$ (between functors $\mathbf{Ar}^{\mathsf{op}}\times\mathbf{ICones}\to\mathbf{ICones}$).

```coq
(* theories/homs/bilin.v — Section LinhomToInt,
   Variables (R : realType) (Ar : MeasSubcat R) (X : ar_obj Ar)
             (B : ICone.type Ar)
             (f : linhom_car Ar (fmeas R (ar_carrier Ar X)) B) *)

Definition linhom_to_int.

Lemma linhom_to_int_E.
```

### Thm 6.1 round-trips (`K_I_int_to_linhom_path_E`, `I_K_int_to_linhom_E`, `int_to_linhom_fun_dirac`, `icone_integral_dirac_path`)

The two cancellation identities are the engines Thm 6.5 consumes. $\mathcal{K}\circ\mathcal{I}=\mathrm{id}$ on paths (`K_I_int_to_linhom_path_E`) is path extensionality (`path_eq`) plus the elementary Dirac evaluation $\mathcal{I}^{B}_X(\beta)(\boldsymbol\delta^{X}(r))=\beta(r)$ (`int_to_linhom_fun_dirac`, proved by Pettis uniqueness and mathcomp-analysis's `integral_dirac`). $\mathcal{I}\circ\mathcal{K}=\mathrm{id}$ on linear maps (`I_K_int_to_linhom_E`) is `linhom` extensionality (`linhom_eq`) plus the *Dirac approximation* $\mu=\int_X\boldsymbol\delta^{X}\,d\mu$ in $\mathsf{FMeas}(X)$ (`icone_integral_dirac_path`) — every finite measure is the Pettis integral of the Dirac path against itself, checked on each measurable $U$ by measure extensionality (`fmeas_eq`) against the test $e_U$, and closed by `integral_indic`. The Dirac approximation is the mathematical content that makes the second round-trip go through; it is a statement about a *single* measure, distinct from the Thm 6.2 density principle `dirac_dense`, which is a statement about two morphisms.

> **Paper — Theorem 6.1** (arXiv 2212.02371, `th:meas-path-equiv`). For each $X\in\mathbf{Ar}$ and integrable cone $B$, $\mathcal{I}^{B}_X$ is an isomorphism, natural in $X$ and in $B$.

```coq
(* theories/homs/bilin.v — Sections RoundTripKI / DiracApprox / RoundTripIK *)

Lemma int_to_linhom_fun_dirac.

Lemma K_I_int_to_linhom_path_E.

Lemma icone_integral_dirac_path.

Lemma I_K_int_to_linhom_E.
```

### Thm 6.2 (`dirac_dense`)

The Dirac masses $\boldsymbol\delta^{X}(r)$ are *dense* in the integrable cone $\mathsf{FMeas}(X)$: any two $\mathbf{ICones}$ morphisms out of $\mathsf{FMeas}(X)$ that agree on every $\boldsymbol\delta^{X}(r)$ coincide. This is the proof engine behind the coalgebra structure of $\mathsf{FMeas}(X)$ and the embedding of $\mathbf{Skern}$; it is a consequence of the path–hom bijection $\mathcal{I}^{B}_X$ of Thm 6.1. Here `Lfun h` is the underlying linear function $\mathsf{cones\_hom\_fun}(\mathsf{mcones\_hom\_cones}(\mathsf{icones\_hom\_mcones}\,h))$ of an `icones_hom`, `dirac_fmeas r` is the Dirac measure $\boldsymbol\delta^{X}(r)\in\mathsf{FMeas}(X)$, and `FMeas X` is $\mathsf{fmeas}\,R\,(\mathsf{ar\_carrier}\,\mathrm{Ar}\,X)$.

> **Paper — Theorem 6.2** (arXiv 2212.02371, `th:dirac-dense`). Let $X\in\mathbf{Ar}$, $B$ be an object of $\mathbf{ICones}$ and $f_1,f_2\in\mathbf{ICones}(\mathsf{FMeas}(X),B)$. If, for all $r\in X$, one has $f_1(\boldsymbol\delta^{X}(r))=f_2(\boldsymbol\delta^{X}(r))$ then $f_1=f_2$.

```coq
(* theories/exp/coalgebra.v — Section Coalgebra, Variables R Ar *)
Lemma dirac_dense (X : ar_obj Ar) (B : ICone.type Ar)
    (f g : icones_hom Ar (FMeas X) B) :
  (forall r : ar_carrier Ar X, Lfun f (dirac_fmeas r) = Lfun g (dirac_fmeas r)) ->
  f = g.
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

### Thm 6.5 Klin (`Skern_to_ICones_obj`, `Skern_to_ICones_mor_E`, `Skern_to_ICones_mor_norm_le1`, `Skern_to_ICones_mor_id`, `Skern_to_ICones_mor_comp`)

$\mathsf{Klin}$ is a genuine functor, not just a family of maps. On objects it is $X\mapsto\mathsf{FMeas}(X)$ (`Skern_to_ICones_obj`); on morphisms $\kappa\mapsto\mathcal{I}^{\mathsf{FMeas}(Y)}_X(\kappa)$, computed by `Skern_to_ICones_mor_E`. Packaging the image as an `icones_hom` needs one fact beyond the five `linhom` fields of Thm 6.1 forward: the *pointwise* norm-decrease constraint $\lVert\mathsf{Klin}(\kappa)(\mu)\rVert\leq\lVert\mu\rVert$ (`Skern_to_ICones_mor_norm_le1`), which is exactly where the substochasticity hypothesis $\lVert\kappa\rVert_{\mathsf{Path}}\leq 1$ is spent, chained with Lem 4.2. Functoriality is then $\mathsf{Klin}(\boldsymbol\delta^{X})=\mathrm{id}$ (`Skern_to_ICones_mor_id`, by the Dirac approximation) and $\mathsf{Klin}(\kappa_2\,\kappa_1)=\mathsf{Klin}(\kappa_2)\circ\mathsf{Klin}(\kappa_1)$ (`Skern_to_ICones_mor_comp`, by integral preservation).

> **Paper — Theorem 6.5** (arXiv 2212.02371). The functor $\mathsf{Klin}:\mathbf{Skern}\to\mathbf{ICones}$ is full and faithful.

```coq
(* theories/kernels/kernel_embedding.v — Sections SkernToICones*,
   Variables (R : realType) (Ar : MeasSubcat R) (X Y : ar_obj Ar)
             (κ : Skern_hom Ar X Y) *)

Definition Skern_to_ICones_obj.

Lemma Skern_to_ICones_mor_norm_le1.

Lemma Skern_to_ICones_mor_E.

Lemma Skern_to_ICones_mor_id.

Lemma Skern_to_ICones_mor_comp.
```

### Thm 6.5 faithful / full (`Skern_to_ICones_faithful`, `Skern_to_ICones_full`)

The regression anchor is the conjunction of two independently useful theorems, each one corollary of one round-trip. **Faithful** (`Skern_to_ICones_faithful`): if $\mathsf{Klin}(\kappa_1)=\mathsf{Klin}(\kappa_2)$ then the underlying `linhom`s agree, and applying $\mathcal{K}$ to both sides gives $\kappa_1=\kappa_2$ by $\mathcal{K}\circ\mathcal{I}=\mathrm{id}$ (`K_I_int_to_linhom_path_E`), lifted from paths to kernels by `Skern_hom_eq`. **Full** (`Skern_to_ICones_full`): given $f\in\mathbf{ICones}(\mathsf{FMeas}(X),\mathsf{FMeas}(Y))$, the candidate kernel is $\kappa:=r\mapsto f(\boldsymbol\delta^{X}(r))$; it is substochastic because $\lVert f(\boldsymbol\delta^{X}(r))\rVert\leq\lVert\boldsymbol\delta^{X}(r)\rVert=1$ (the section-local helper `icones_to_skern_norm_le1`, from `cones_hom_norm_le1` and `dirac_fmeas_norm`), and $\mathsf{Klin}(\kappa)=f$ by $\mathcal{I}\circ\mathcal{K}=\mathrm{id}$ (`I_K_int_to_linhom_E`) after re-viewing $f$ as a `linhom` with operator-norm constant $1$ (the section-local helper `icones_to_linhom`) — the packaged conclusion being `Skern_to_ICones_mor_to_skern`, read back to morphisms by `icones_hom_eq`.

> **Paper — Theorem 6.5** (arXiv 2212.02371). The functor $\mathsf{Klin}:\mathbf{Skern}\to\mathbf{ICones}$ is full and faithful.

> **Difference.** The paper states one theorem; the development proves the two halves separately and bundles them in `Skern_to_ICones_fully_faithful`. *Why:* each half is a reusable statement in its own right (faithfulness is what identifies a kernel with its integration map, fullness is what produces a kernel from an arbitrary $\mathbf{ICones}$ morphism), and keeping them apart keeps the regression anchor a one-line combination whose `Print Assumptions` output is easy to attribute. The two helpers `icones_to_linhom` and `icones_to_skern_norm_le1` are `Local` to the fullness section — they are named here for the reader but are not exported.

```coq
(* theories/kernels/kernel_embedding.v — Sections SkernToIConesFaithful / Full *)

Theorem Skern_to_ICones_faithful.

Lemma Skern_to_ICones_mor_to_skern.

Theorem Skern_to_ICones_full.
```

---

## Paper § 7 — Stable functions and the cartesian-closed category SCones

| Paper | English statement | Rocq |
|---|---|---|
| §7.0 | Completeness at an arbitrary radius: a $\leq$-increasing chain bounded by $M>0$ has a supremum $\mathsf{cone\_sup\_at}\,M$, and the radius-aware Scott-continuity built on it; every linear unit-ball $\omega$-continuous map is Scott-continuous. | `cone_sup_at`, `cone_sup_at_ub`, `cone_sup_at_lub`, `cone_sup_at_norm`, `cone_sup_at_ball`, `cone_sup_at_indep`, `is_scott_continuous`, `linear_scott_of_omega`, `addr_scott_continuous`, `scaler_scott_continuous`, `comp_scott_continuous` — `theories/cones/omega_general.v` |
| Lem 7.1 | The gauge $N$ is a norm on the local cone $P=B_x$, and $P$ is a cone whose $0$, operations and order are those of $\mathcal{M}B$. | `local_cone` (`isCone.Build`), `lc_normh`, `lc_normt` — `theories/stable/local_cone.v` |
| Lem 7.2 | For $u\in\mathcal{M}B_x\setminus\{0\}$: $x+\lVert u\rVert^{-1}u$ stays in the unit ball, and $x+\lambda u$ leaves it for $\lambda>\lVert u\rVert^{-1}$. | `gauge_sup_reach`, `gauge_sup_gt_out` — `theories/stable/local_cone.v` |
| Lem 7.4 | The reindexing $\mathrm{in}_j$ is a parity-preserving bijection between $\mathcal{P}^{\epsilon}(n)$ and $\{J\in\mathcal{P}^{\epsilon}(n+1)\mid j\in J\}$. | `Ppos_split_in`, `Pneg_split_in`, `Ppos_split_out`, `Pneg_split_out` — `theories/stable/findiff.v` |
| Def 7.5 | A function $f:\mathcal{B}P\to Q$ is *totally monotonic* if its iterated finite differences over the parity lattice satisfy $\sum_{I\in\mathcal{P}^-(n)}f(x+\sum_{i\in I}u_i)\le\sum_{I\in\mathcal{P}^+(n)}f(x+\sum_{i\in I}u_i)$. | `is_totmono`, `Pneg`/`Ppos` — `theories/stable/totmono.v` |
| Def 7.7 | A function is *stable* if it is totally monotonic, bounded, and $\omega$-continuous on the unit ball. | `is_stable` (uses `is_scott_continuous_unit`) — `theories/stable/totmono.v` |
| Def 7.10 | A *measurable stable* function additionally sends measurable paths $X\to C$ to measurable paths $X\to D$. | `is_meas_stable` — `theories/stable/totmono.v` |
| Lem 7.11 | The stable and measurable functions $C\to D$ form a precone under pointwise operations (closed under $0$, addition, and non-negative scaling). | `stable_zero`, `stable_add`, `stable_scale` — `theories/stable/totmono.v` |
| §7.2 hom | The carrier of the stable internal hom $B\Rightarrow_s C$: a measurable stable function bundled with the canonical $0$-extension off the unit ball; the pointwise operations make it the precone $P$ of Lemma 7.11. | `stablehom`, `sh_fun`, `sh_meas_stable`, `sh_offball`, `stablehom_eq` (+ the `isPrecone` instance) — `theories/stable/stablehom.v` |
| Lem 7.12 | The stable (cone) order coincides with the alternating finite-difference inequality: $f\le g$ iff a sign-split difference test holds. | `sh_le_of_alt`, `sh_le_pointwise`, `sh_diff` — `theories/stable/stablehom.v` |
| §7.2 norm | $B\Rightarrow_s C$ is equipped with the operator norm $\lVert f\rVert=\sup_{x\in\mathcal{B}C}\lVert f(x)\rVert$, well defined because stable functions are bounded; it satisfies (Normh), (Normt), (Normp) and (Normz). | `sh_norm`, `sh_norm_ub`, `sh_norm_lub`, `sh_normh`, `sh_normt`, `sh_normp`, `sh_normz` — `theories/stable/stablehom.v` |
| Lem 7.14 | An increasing sequence of stable maps has a pointwise supremum which is again bounded, totally monotonic, $\omega$-continuous and measurable, and which is its least upper bound — the (Normc) axiom for $B\Rightarrow_s C$. | `sh_sup`, `sh_sup_ball_ub`, `sh_sup_ball_lub`, `sh_sup_ball_norm` (+ the `isCone` instance) — `theories/stable/stablehom.v` |
| §7.2 icone | $B\Rightarrow_s C$ is a *measurable* cone for the $\gamma\triangleright m$ test family and an *integrable* cone for the pointwise Pettis integral $f(x)=\int_{r\in X}\eta(r)(x)\,\mu(dr)$. | `sh_mcone_M`, `sh_mcone_M_comp`, `sh_mcone_M_sep`, `sh_mcone_M_norm`, `sh_int_fun`, `sh_int_fun_totmono`, `sh_int_fun_scott`, `sh_int_car_pettis`, `sh_int_exists` (+ the `isMCone` / `isICone` instances) — `theories/stable/stablehom.v` |
| §7.3 diff | The signed difference operators $\Delta^{+}f(\overrightarrow{u})$, $\Delta^{-}f(\overrightarrow{u})$ and their pointwise cone difference $\Delta f(\overrightarrow{u}):\mathcal{B}\mathcal{M}B_{\overrightarrow{u}}\to\mathcal{M}C$, with the well-definedness that total monotonicity supplies. | `Delta_arg`, `Delta_pos`, `Delta_neg`, `Delta`, `Delta_E`, `Delta_neg_le_pos` — `theories/stable/findiff.v` |
| Def 7.15 | $f$ is *$n$-increasing* if it is increasing and each single-step difference $\Delta f(u)$ over the local cone $B_u$ is $(n-1)$-increasing. | `is_n_increasing` (Fixpoint on $n$) — `theories/stable/findiff.v` |
| Lem 7.16 | If $f$ is $n$-increasing for all $n$, then so is each single-step difference $\Delta f(u):\mathcal{B}\mathcal{M}B_u\to\mathcal{M}C$. | `is_n_increasing_Delta` — `theories/stable/findiff.v` |
| Lem 7.18 | If $f$ is totally monotonic, then so is each single-step difference $\Delta f(u):\mathcal{B}\mathcal{M}B_u\to\mathcal{M}C$. | `totmono_Delta1` — `theories/stable/findiff.v` |
| Thm 7.19 | $f$ is totally monotonic iff it is *$n$-increasing* for every $n\in\mathbb{N}$. | `totmono_is_n_increasing` (forward), `is_n_increasing_totmono` (converse) — `theories/stable/findiff.v` |
| Lem 7.20–7.25 | The finite-difference / sign-split machinery $\Delta^{\epsilon}$, $\Delta$, $\mathsf{S}^n B$ used to prove Thm 7.19 and the §7.3 closure properties. | `totmono_Delta_pos`, `totmono_Delta_neg`, `totmono_Delta`, `SD`, `SD_Delta`, `SD_cons`, `SD_add`, `SD_perm`, `SD_mono_centre`, `SD_mono_full`, `SD_diag`, `SD_723`, `SnB`, `SnB_increasing` — `theories/stable/findiff.v` + `theories/stable/compose.v` |
| Lem 7.21 | For totally monotonic $f$, the iterated difference is bounded above by $f$ at the summed point: $\Delta f(\overrightarrow{u})(x)\le f(x+\sum_i u_i)$. | `Delta_le`, `SD_le` — `theories/stable/findiff.v` |
| Lem 7.26 | Faà-di-Bruno composition: $k(x)=\Delta g(h_1 x,\dots,h_n x)(f x)$ is totally monotonic when $g,f,h_i$ are and $f+\sum_i h_i$ stays in the unit ball. | `ninc_kfun`, `totmono_comp` — `theories/stable/compose.v` |
| Lem 7.27 | If $f$ is linear in its first argument and totally monotonic in its second, it is totally monotonic on the product of unit balls. | `ev_totmono` (delivered in the form actually needed by the CCC) — `theories/stable/scones_ccc.v` |
| Thm 7.30 | Stable (and measurable) functions of norm $\le 1$ are closed under composition. | `stable_comp`, `meas_stable_comp` — `theories/stable/compose.v` |
| Cat 7 | $\mathbf{SCones}$ is a category: objects the integrable cones, morphisms the measurable stable maps of operator norm $\leq 1$, with identity, composition and the three category laws. | `scones_hom`, `sc_norm`, `sc_norm_ub`, `sc_norm_lub`, `scones_hom_eq`, `scones_id`, `scones_comp`, `scones_compIl`, `scones_compIr`, `scones_compA` — `theories/stable/scones_cat.v` |
| Lem 7.31 | $\mathbf{ICones}(B,C)\subseteq\mathbf{SCones}(B,C)$: every linear morphism is stable, giving the forgetful functor $\mathsf{Der}$. | `linear_totmono`, `linear_scott_unit`, `linear_stable`, `icones_meas_stable`, `ders`, `ders_id`, `ders_comp`, `ders_faithful` — `theories/stable/scones_cat.v` |
| §7.4 products | The $\mathbf{ICones}$ product $\mathop{\&}_{i\in I}B_i$ is also the $I$-indexed product in $\mathbf{SCones}$: projections $\mathsf{Der}(\mathrm{pr}_i)$, the $0$-extended tupling $\langle f_i\rangle$, and its universal property as a pair of Leibniz equalities. | `scones_proj`, `scones_tuple`, `scones_tuple_bd`, `cones_prod_val_big`, `cones_prod_le_compI`, `scones_tuple_proj`, `scones_tuple_unique` — `theories/stable/scones_cat.v` |
| Thm 7.32 | The category $\mathbf{SCones}$ of stable functions has all products and is cartesian closed. | `SCones_ccc`, `SCones_CCC` (record + witness) — `theories/stable/scones_ccc.v` |
| Thm 7.34 | The forgetful functor $\mathsf{Der}:\mathbf{ICones}\to\mathbf{SCones}$ preserves all limits. | `der_preserves_prod_proj`, `der_preserves_limits` — `theories/stable/der_continuous.v` |
| (also) | Stable functions admit a least fixpoint via the cone unit-ball $\omega$-cpo (paper §9.2). | `lfp_fixpoint`, `sfix_fixpoint`, `Yfix`, `Yfix_fix` — `theories/stable/fixpoint.v` |

The `is_stable` predicate uses `is_scott_continuous_unit` (unit-ball input,
any-radius output sup) because the strictly-linear `is_omega_continuous`
(both $\omega$-chains in the unit ball) is **not preserved under non-negative
scaling for non-linear maps** — a faithful reading of the paper's setting,
not a weakening.

### §7.0 (`cone_sup_at`, `is_scott_continuous`, `linear_scott_of_omega`)

The cone mixin materialises completeness only on the unit ball: `cone_sup_ball` takes an increasing chain bounded by $1$, and the matching `is_omega_continuous` of §2 constrains *both* the input and the image chain to that ball. §7 needs the same calculus at an arbitrary radius, so `theories/cones/omega_general.v` builds it. `cone_sup_at M u` is the supremum of a $\leq$-increasing chain bounded by $M>0$, obtained by rescaling into $\mathcal{B}P$ by $1/M$, taking `cone_sup_ball` there, and scaling back by $M$; `cone_sup_at_ub`, `cone_sup_at_lub` and `cone_sup_at_norm` are its upper-bound, least-upper-bound and norm characterisations, `cone_sup_at_ball` shows it agrees with `cone_sup_ball` at radius $1$, and `cone_sup_at_indep` shows the value is independent of which admissible radius is used. `is_scott_continuous f` is commutation of $f$ with `cone_sup_at` at any input radius $M$ and image radius $M_f$, and `linear_scott_of_omega` is the reusable bridge — a linear, unit-ball $\omega$-continuous map is Scott-continuous — proved by rescaling both chains at the single common radius $K:=\max(M,M_f)$ and swapping back with `cone_sup_at_indep`. The corollaries `addr_scott_continuous` / `addl_scott_continuous`, `scaler_scott_continuous` and `comp_scott_continuous` record that translation, scaling and composition are Scott-continuous; the scaling one is what makes `stable_scale` (Lem 7.11) go through for *every* $r$. The same file carries the *consolidated sup-calculus* — chain monotonicity `precone_chain_le`, proof-irrelevance `cone_sup_ball_irr`, the diagonal sup-addition identity `cone_sup_at_addD`, the iterated-(Normt) bound `cone_norm_sum`, the finite-sum supremum `cone_sum_sup` / `cone_sum_sup_eq` and the scaled chain `scale_chain_sup` — each proved once at a general radius, with the radius-$1$ corollaries in the shape `linhom.v`, `totmono.v`, `stablehom.v`, `findiff.v` and `scones_ccc.v` consume.

> **Paper — Definition 2.2** (arXiv 2212.02371). $f$ is *$\omega$-continuous*, or simply *continuous* (no other notion of continuity will be considered in this paper), if $f$ is monotonic and for each bounded increasing sequence $(x_n)_{n\in\mathbb{N}}$ of elements of $A$, one has $f(\sup_{n\in\mathbb{N}}x_n)=\sup_{n\in\mathbb{N}}f(x_n)$, that is $f(\sup_{n\in\mathbb{N}}x_n)\leq\sup_{n\in\mathbb{N}}f(x_n)$ since the converse holds by monotonicity of $f$.

> **Difference.** The paper states $\omega$-continuity for an $\omega$-closed subset $A\subseteq P$ and *arbitrary bounded* increasing sequences, so no radius ever appears in it; the mechanised (Normc) axiom instead materialises the supremum as an operator on the *unit ball* only (`cone_sup_ball`, see the Def 2.2 Difference note). A radius-aware layer therefore has to be built before §7 can start. *Why it cannot be avoided:* for a **linear** map every bounded chain rescales into $\mathcal{B}P$ and back, so the unit-ball notion loses nothing — which is why §§2–6 never need this file. A **non-linear** stable $f$ scaled by $r<1$ has an image chain of norm up to $1/r>1$, which leaves the ball and cannot be rescaled back pointwise. Hence `is_stable` uses the unit-*input* form `is_scott_continuous_unit` (input chain in $\mathcal{B}P$, image supremum at any radius — `theories/stable/totmono.v`), which is exactly `is_scott_continuous` specialised to input radius $1$ through `cone_sup_at_ball`. The fully general `is_scott_continuous` would be *too strong* for stable maps: they are monotone only on $\mathcal{B}P$, so for an input chain leaving the ball the image chain need not even be increasing.

> **Difference.** The radii $M$, $M_f$ and *all* chain side-conditions are explicit arguments of `is_scott_continuous`, mirroring `is_omega_continuous`. This is deliberate: the image-chain hypotheses cannot be derived from $f$ alone, since a map increasing on the radius-$M$ ball need not send it into the radius-$M_f$ ball.

```coq
(* theories/cones/omega_general.v — Section ConeSupAt, Variables R : realType, P : coneType R *)

(* The general-radius supremum: rescale into [B_P] by [1/M], take
   [cone_sup_ball] there, scale back by [M]. *)
Definition cone_sup_at (M : {nonneg R}) (u : nat -> P) (* + chain / bound / 0 < M *) : P.

Lemma cone_sup_at_ub (M : {nonneg R}) (u : nat -> P) n : (* uₙ ≤ cone_sup_at M u *).
Lemma cone_sup_at_lub (M : {nonneg R}) (u : nat -> P) y : (* least such *).
Lemma cone_sup_at_norm (M : {nonneg R}) (u : nat -> P) : (* ‖·‖ ≤ M *).

(* Change of working radius, and agreement with [cone_sup_ball] at radius 1. *)
Lemma cone_sup_at_indep (M M' : {nonneg R}) (u : nat -> P) : (* same supremum *).
Lemma cone_sup_at_ball (u : nat -> P) : (* = cone_sup_ball u *).

(* Section ScottContinuous, Variables P Q : coneType R *)
Definition is_scott_continuous (f : P -> Q) : Prop.

(* Section LinearScott — the reusable bridge, proved by rescaling at K = max M Mf. *)
Lemma linear_scott_of_omega (f : P -> Q) :
  is_linear f -> is_omega_continuous f -> is_scott_continuous f.

(* Section Corollaries / Section Composition. *)
Lemma addr_scott_continuous (y : P) :
  is_scott_continuous (fun x : P => precone_add x y).
Lemma scaler_scott_continuous (r : {nonneg R}) :
  is_scott_continuous (fun x : P => precone_scale r x).
Lemma comp_scott_continuous (f : P -> Q) (g : Q -> S) : (* g ∘ f Scott-continuous *).

(* The consolidated sup-calculus (closing sections of the file). *)
Lemma cone_sup_at_addD (M : {nonneg R}) a b : (* diagonal sup-addition *).
Lemma cone_norm_sum : (* iterated (Normt) bound on a finite cone-sum *).
Lemma cone_sum_sup_eq (A : {set T}) : (* finite sum of general-radius sups *).
Lemma scale_chain_sup (z : P) : (* sup of the scaled chain m ↦ λₘ · z is z *).
```

### Lem 7.1 (`local_cone`, `lc_normh`, `lc_normt`)

The local cone $B_x$ of $B$ at $x\in\mathcal{B}\mathcal{M}B$ is the set of directions $u$ with $x+\lambda u\in\mathcal{B}\mathcal{M}B$ for some $\lambda>0$; equipped with the gauge norm $N(u)=(\sup\{\lambda>0\mid x+\lambda u\in\mathcal{B}\mathcal{M}B\})^{-1}$ it is a cone whose $0$, algebraic operations and order are inherited from $\mathcal{M}B$. The algebraic half is the `isPrecone` instance, the norm laws are `lc_normh` (homogeneity) and `lc_normt` (sub-additivity), and the whole is assembled into the `isCone` HB instance on `local_cone x`. Two supporting facts carry the norm: `gauge_set_ub` bounds the admissible-scale set (for $u\neq0$ every admissible $s$ satisfies $s\le\lVert u\rVert_B^{-1}$, so the supremum defining $N$ exists), and `lc_val_norm_le` is the paper's $\lVert u\rVert_B\le\lVert u\rVert_{B_x}$ — the inequality that later lets every $B$-test pull back to a $B_x$-test. (Normc) is `lc_sup_ball_translate`: the $B_x$-supremum of a chain is read off the $B$-supremum of the *translated* chain $n\mapsto x+u_n$.

The same file continues past Lemma 7.1 into the paper's **Example 7.3** ("$B_x$ computed as in $B$"), which has no card of its own: `lc_mcone_M` is the test family — scaled pullbacks $(r,u)\mapsto c\cdot m(r,\mathsf{lc\_val}\,u)$ of $B$-tests — with its three closure axioms `lc_mcone_M_comp` (Mscomp, reindexing), `lc_mcone_M_sep` (Mssep, separation via the bare $c=1$ pullbacks) and `lc_mcone_M_norm` (Msnorm, the renormalised test reaching within $\varepsilon$ of the gauge norm); `lc_icone_exists` then discharges the `isICone` existence obligation by integrating through the inclusion into $B$. So $B_x$ is a full `iconeType` at any strict-interior point.

> **Paper — Lemma 7.1** (arXiv 2212.02371, `lemma:local-cone-is-a-subcone`). The function $N$ is a norm on $P$ and, equipped with this norm, $P$ is a cone whose $0$ element and algebraic operations are those of $\mathcal{M}B$.

> **Difference — strict interior.** Every section of `local_cone.v` carries the hypothesis `Hx : cone_norm x < 1`, a *strict* bound, where the paper's Lemma 7.1 asks only for $x\in\mathcal{B}\mathcal{M}B$, i.e. $\lVert x\rVert\le 1$. *Why:* the split is between the two layers. The algebraic and cone development — the `isPrecone` instance, the gauge norm, Lemmas 7.1 and 7.2 — needs only $\lVert x\rVert\le 1$ and a `coneType`. The measurability and integrability layer of Example 7.3 (“$B_x$ computed as in $B$”) needs $B$ measurable resp. integrable **and** the strict bound: it is $\lVert x\rVert<1$ that leaves room to renormalise a pulled-back $B$-test and so closes the simplified `mcone_M_norm` field of `mcone.v` for `lc_mcone_M` (`lc_mcone_M_norm`). Rather than run two hypothesis regimes, the formalisation strengthens the section hypothesis to the strict bound throughout and recovers the $\le 1$ facts the cone development consumes as `Hxle := ltW Hx`; nothing in the meaning of Lemmas 7.1/7.2 changes. This loses no generality for the paper's purposes — local cones are used exactly for differentiation *at interior points* — and it is precisely where the linear development's simplified norm condition becomes satisfiable without weakening any cone axiom. The same strict bound is what the §7.3 differentiation cards inherit, since every one of them differentiates over a local cone: an `Hsu : ‖su‖ < 1` in a `findiff.v` or `compose.v` section header (see Lem 7.18, Lem 7.21) is *this* hypothesis reappearing as the argument `lc_coneType` demands — it is not an extra restriction invented by those lemmas, and the corresponding paper statements carry no strictness.

```coq
(* theories/stable/local_cone.v — Variables: R : realType, B : coneType R, x : B *)
(* The section hypothesis: STRICT interior (see the Difference above). *)
Hypothesis Hx : cone_norm x < 1.

Definition local_cone : Type := { u : B | localP u }.

(* Paper Lemma 7.1 (algebraic half): B_x is a precone whose 0 and
   operations are inherited from B. *)
HB.instance Definition _ := @isPrecone.Build R local_cone
  lc_zero lc_add lc_scale lc_addA lc_addC lc_add0
  lc_scale_DAr lc_scale_DAl lc_scale_A lc_scale_1
  lc_scale_0r lc_scale_0l lc_cancel lc_pos.

Lemma lc_normh (r : {nonneg R}) (u : P) :
  lc_norm (lc_scale Hx r u) = r%:num * lc_norm u.

Lemma lc_normt (u1 u2 : P) :
  lc_norm (lc_add u1 u2) <= lc_norm u1 + lc_norm u2.

(* The gauge set is bounded above, so its sup — hence N — exists. *)
Lemma gauge_set_ub : (* lc_val u <> 0 -> has_ubound (gauge_set u) *).

(* Paper §7.1, p. 1:56: ‖u‖_B ≤ ‖u‖_{B_x}. *)
Lemma lc_val_norm_le : (* cone_norm (lc_val u) <= lc_norm u *).

(* (Normc): the B_x-sup is the B-sup of the translated chain n ↦ x + uₙ. *)
Lemma lc_sup_ball_translate : (* x + lc_val (cone_sup_ball u ..) = cone_sup_ball (x + u ..) *).

(* Paper Lemma 7.1: B_x is a cone, norm the gauge lc_norm. *)
HB.instance Definition _ := @isCone.Build R (local_cone x)
  lc_norm
  lc_normh
  (fun (u : P) (H : lc_norm u = 0) => @lc_eq R B x u (lc_zero Hx) (lc_normz H))
  lc_normt
  (* (Normp) + (Normc) via lc_normp / lc_sup_ball, transported through lc_leE *)
  _ _ _ _ _.

(* --- Paper Example 7.3: "B_x computed as in B" (needs ‖x‖ < 1) --- *)

(* theories/stable/local_cone.v — Section LocalMCone: R, Ar, B : MCone.type Ar, x, Hx *)
(* The test family: scaled pullbacks of B-tests along lc_val. *)
Definition lc_mcone_M (Y : ar_obj Ar) : set (test_of Ar Y LC).

Lemma lc_mcone_M_comp : (* (Mscomp): closed under reindexing *).
Lemma lc_mcone_M_sep  : (* (Mssep): arity-0 tests separate points of B_x *).
Lemma lc_mcone_M_norm : (* (Msnorm): the renormalized test reaches ‖u‖ − ε *).

(* theories/stable/local_cone.v — Section LocalICone *)
(* The isICone obligation: paths into B_x are integrable, via lc_val. *)
Lemma lc_icone_exists : (* is_measurable_path β -> forall µ, is_path_integrable β µ *).
```

### Lem 7.2 (`gauge_sup_reach`, `gauge_sup_gt_out`)

The gauge norm on the local cone measures how far the direction $u$ can be scaled before leaving the unit ball: the reach $x+\lVert u\rVert_{B_x}^{-1}u$ still lies in $\mathcal{B}\mathcal{M}B$ (`gauge_sup_reach`), and any strictly larger scale leaves it (`gauge_sup_gt_out`).

> **Paper — Lemma 7.2** (arXiv 2212.02371, `lemma:cloc-norm-charact`). Let $x\in\mathcal{B}\mathcal{M}B$ and $u\in\mathcal{M}B_x\setminus\{0\}$. Then we have $x+\lVert u\rVert_{B_x}^{-1}\,u\in\mathcal{B}\mathcal{M}B$ and $x+\lambda u\notin\mathcal{B}\mathcal{M}B$ for all $\lambda>\lVert u\rVert_{\mathcal{M}B_x}^{-1}$.

> **Difference.** The mechanisation phrases the reach through $\mathsf{gauge\_sup}\,u=\lVert u\rVert_{B_x}^{-1}$ (the supremum of admissible scales) rather than the norm $\lVert u\rVert_{B_x}$ directly; the reach point is $x+(\mathsf{gauge\_sup}\,u)\cdot u$ and the "out" half is stated for any $\mathsf{gauge\_sup}\,u<s$.

```coq
(* theories/stable/local_cone.v — Variables: R B x; P := local_cone x *)
Definition gauge_sup (u : P) : R := sup (gauge_set u).

Lemma gauge_sup_reach (u : P) (Hu0 : lc_val u <> precone_zero) :
  cone_norm (precone_add x
     (precone_scale (NngNum (gauge_sup_ge0 u)) (lc_val u))) <= 1.

Lemma gauge_sup_gt_out (u : P) (s : {nonneg R}) :
  lc_val u <> precone_zero ->
  gauge_sup u < s%:num ->
  ~ cone_norm (precone_add x (precone_scale s (lc_val u))) <= 1.
```

### Lem 7.4 (`Ppos_split_in`, `Pneg_split_in`, `Ppos_split_out`, `Pneg_split_out`)

The reindexing $\mathrm{in}_j$ inserts the element $j$ into a parity set while shifting the elements above $j$, and gives a parity-preserving bijection between $\mathcal{P}^{\epsilon}(n)$ and the sets of $\mathcal{P}^{\epsilon}(n+1)$ containing $j$. In the mechanisation this is packaged (at $j=$ `ord0`) as four `finset` image equalities: the $j\in J$ halves (`Ppos_split_in`, `Pneg_split_in`) and the $j\notin J$ halves (`Ppos_split_out`, `Pneg_split_out`).

> **Paper — Lemma 7.4** (arXiv 2212.02371, `lemma:inset-corresp`). Let $n\in\mathbb{N}$, $j\in\{1,\dots,n+1\}$ and $\epsilon\in\{-,+\}$. Given $I\in\mathcal{P}^{\epsilon}(n)$, the set $\mathrm{in}_j(I)=\{i\in I\mid i<j\}\cup\{j\}\cup\{i+1\mid i\in I\text{ and }i\geq j\}$ belongs to $\mathcal{P}^{\epsilon}(n+1)$ and $\mathrm{in}_j$ defines a bijection between $\mathcal{P}^{\epsilon}(n)$ and $\{J\subseteq\{1,\dots,n+1\}\mid J\in\mathcal{P}^{\epsilon}(n+1)\text{ and }j\in J\}$.

> **Difference.** The paper states the bijection for an arbitrary $j$; the mechanisation specialises to $j=$ `ord0` (the only instance the finite-difference recurrences use) and records the correspondence as image (`imset`) equalities of finsets, discharged by `big_imset` in the difference recurrences.

```coq
(* theories/stable/findiff.v *)
Lemma Ppos_split_in :
  [set I in Ppos n.+1 | ord0 \in I] = [set injI0 J | J in Ppos n].

Lemma Pneg_split_in :
  [set I in Pneg n.+1 | ord0 \in I] = [set injI0 J | J in Pneg n].

Lemma Ppos_split_out :
  [set I in Ppos n.+1 | ord0 \notin I] = [set injI J | J in Pneg n].

Lemma Pneg_split_out :
  [set I in Pneg n.+1 | ord0 \notin I] = [set injI J | J in Ppos n].
```

### Def 7.5 (`is_totmono`, `Pneg`, `Ppos`)

Total monotonicity is an inclusion-exclusion inequality over the odd- and even-parity subsets $\mathcal{P}^-(n)$, $\mathcal{P}^+(n)$ of $\{1,\dots,n\}$, generalizing absolute monotonicity to cones. `Pneg`/`Ppos` partition the powerset of $\{1,\dots,n\}$ by the parity of $n-\lvert I\rvert$; the `powerset` guard in the two definitions is vacuous (every `I : {set 'I_n}` is a subset of the full set), so membership unfolds to the bare parity test by `in_Pneg` / `in_Ppos`, `in_Pneg_Ppos` records that the two families are complementary, and `Ppos_setT` is the paper's remark that $\{1,\dots,n\}\in\mathcal{P}^+(n)$. The two sums of (7.1) are `\sumP`-notation `bigop`s over the `precone_add` monoid, so their algebra is the `bigop` algebra: `sumP_add` splits a sum of pointwise sums (this is `big_split`) and `sumP_scale` pulls a non-negative scalar out (`big_morph` for the semimodule action). Those two are what make the Lem 7.11 closure proofs one-liners. Two sanity instances pin the definition to its familiar readings: `totmono_increasing` is $n=1$ — total monotonicity implies increasingness on the ball — and `totmono2` is the raw $n=2$ inequality $f(x+u_0)+f(x+u_1)\le f(x+u_0+u_1)+f(x)$.

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

(* Membership is the bare parity test; the two families are
   complementary; and {1,…,n} sits on the positive side. *)
Lemma in_Pneg (n : nat) (I : {set 'I_n}) : (I \in Pneg n) = odd (n - #|I|).
Lemma in_Ppos (n : nat) (I : {set 'I_n}) : (I \in Ppos n) = ~~ odd (n - #|I|).
Lemma in_Pneg_Ppos (n : nat) (I : {set 'I_n}) : (I \in Ppos n) = ~~ (I \in Pneg n).
Lemma Ppos_setT (n : nat) : [set: 'I_n] \in Ppos n.

(* Section ConeSumLemmas — the bigop algebra of the (7.1) sums. *)
Lemma sumP_add : (* Σ_(i in A) (f i + g i) = Σ f + Σ g *).
Lemma sumP_scale : (* r *: Σ_(i in A) f i = Σ_(i in A) r *: f i *).

(* Sanity instances: n = 1 is increasingness, n = 2 is the familiar
   f(x+u₀) + f(x+u₁) ≤ f(x+u₀+u₁) + f x. *)
Lemma totmono_increasing : (* is_totmono f -> increasing on the ball *).
Lemma totmono2 : (* the raw (7.1) inequality at n = 2 *).
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

The stable (and measurable) functions $C\to D$, equipped with pointwise algebraic operations, form a precone; the three lemmas record closure under $0$, addition, and non-negative scaling. Each packaged lemma is the conjunction of its clauses, proved separately and in the same order as `is_stable`. For addition: total monotonicity is `totmono_add` (split both (7.1) sums with `sumP_add`, then add the two orders), boundedness is the sum of the bounds, and $\omega$-continuity rests on the *radius-aware diagonal-sup identity* `sup_at_addD` — the sup of a diagonal sum is the sum of the sups at a common radius $M$, which is `cone_sup_at_addD` of `omega_general.v` re-exported under a local name for this file. For scaling: `totmono_scale` (factor $r$ out with `sumP_scale`, then `precone_scale_le`) and the bound $r\cdot M$. On the measurable side the extra path-preservation clause is `meas_stable_add` and `meas_stable_scale`, each reducing to the fact that measurable paths are closed under pointwise addition resp. non-negative scaling.

> **Paper — Lemma 7.11** (arXiv 2212.02371). The set of stable and measurable functions $C\to D$, equipped with algebraic operations defined pointwise, is a precone.

```coq
(* theories/stable/totmono.v *)
Lemma stable_zero : is_stable stm_zero.

Lemma stable_add (f g : P -> Q) :
  is_stable f -> is_stable g -> is_stable (stm_add f g).

Lemma stable_scale (r : {nonneg R}) (f : P -> Q) :
  is_stable f -> is_stable (stm_scale r f).

(* The clauses those two package. *)
Lemma totmono_add : (* is_totmono f -> is_totmono g -> is_totmono (f + g) *).
Lemma totmono_scale : (* is_totmono f -> is_totmono (r *: f) *).

(* Section DiagonalSup — the ω-continuity clause of stable_add: the
   radius-aware diagonal-sup identity, = omega_general.cone_sup_at_addD. *)
Lemma sup_at_addD : (* sup (a + b) = sup a + sup b at a common radius M *).

(* The measurable half: path preservation is closed under + and r *: . *)
Lemma meas_stable_add : (* is_meas_stable f -> is_meas_stable g -> is_meas_stable (f + g) *).
Lemma meas_stable_scale : (* path preservation survives r *: f *).
```

### §7.2 hom (`stablehom`, `sh_meas_stable`, `sh_offball`, `stablehom_eq`)

The precone $P$ of Lemma 7.11 is realised as a *carrier record*: an element of $B\Rightarrow_s C$ is a function $f:B\to C$ (`sh_fun`, a coercion) together with a proof that it is measurable stable (`sh_meas_stable`) and the canonical $0$-extension field `sh_offball`, forcing $f(x)=0$ whenever $\lVert x\rVert>1$. All three proof fields are `Prop`, so `stablehom_eq` reduces equality of two elements to equality of the underlying functions. The pointwise operations `sh_zero` / `sh_add` / `sh_scale` — the packaged form of the Lem 7.11 closure lemmas — carry the eleven precone axioms and are registered as the `isPrecone` HB instance on `stablehom B C`, so $B\Rightarrow_s C$ is a `preconeType R`. (The Lem 7.11 entry above documents the *predicate-level* closure; this entry documents the object those lemmas assemble into.)

> **Paper — Lemma 7.11** (arXiv 2212.02371, LMCS 21(1:1), p. 1:58). The set of stable and measurable functions $C\to D$, equipped with algebraic operations defined pointwise, is a precone. […] This is straightforward, we use $P$ for this precone.

> **Difference.** The paper's stable maps are functions $f:\mathcal{B}C\to D$ defined *only on the unit ball*, with two of them equal iff they agree on $\mathcal{B}C$. The mechanisation keeps a **total** carrier $B\to C$ and adds the canonical $0$-extension field `sh_offball`. Since `is_meas_stable` constrains $f$ only on the unit ball, the off-ball behaviour is then fully determined ($f=0$ there), so Leibniz equality coincides with the paper's agreement-on-$\mathcal{B}C$. *Why it matters:* this is exactly what unblocks the (Normz) cone axiom — a norm-zero map is $0$ on the ball by the supremum and $0$ off the ball by `sh_offball`, hence identically $0$ (see the §7.2 norm entry). The same device is used for `SCones` morphisms (see Cat 7).

```coq
(* theories/stable/stablehom.v — Section StablehomCar, Variables R : realType, Ar : MeasSubcat R, B C : MCone.type Ar *)
Record stablehom : Type := MkStablehom { (* sh_fun / sh_meas_stable / sh_offball *) }.

(* Proof-irrelevant extensionality: same underlying function ⇒ equal. *)
Lemma stablehom_eq (f g : stablehom) :
  (forall x, sh_fun f x = sh_fun g x) -> f = g.

(* Paper Lemma 7.11 packaged: the pointwise operations and the eleven
   precone axioms — [stablehom B C : preconeType R]. *)
HB.instance Definition _ := @isPrecone.Build R (stablehom B C) (* sh_zero / sh_add / sh_scale + axioms *).
```

### Lem 7.12 (`sh_le_of_alt`, `sh_le_pointwise`, `sh_diff`)

The cone (stable) order on the precone of stable functions is characterized by a finite-difference inequality between $f$ and $g$; `sh_le_of_alt` is the backward direction — the alternating-sum inequality implies the pointwise stable (precone) order. The forward direction is `sh_le_pointwise` — the stable order implies the pointwise order in $C$, which is the engine for (Normp) and for the sup-ball construction. The witness that makes the backward direction constructive is `sh_diff`, the difference $g\ominus f$ packaged again as a `stablehom` (paper: "*we can define a function $h:\mathcal{B}C\to D$ by $h(x)=g(x)-f(x)$ and this function is totally monotonic*"); `sh_add_diff` is the equation $f+(g\ominus f)=g$ from which `sh_le_of_alt` reads off $f\leq g$.

> **Paper — Lemma 7.12** (arXiv 2212.02371, `lemma:stable-order-charact`). Let $f,g\in P$. One has $f\leq g$ iff for each $n\in\mathbb{N}$ and each $x,u_1,\dots,u_n\in\mathcal{B}\underline{C}$ such that $x+\sum_{i=1}^n u_i\in\mathcal{B}\underline{C}$ one has $$\sum_{I\in\mathcal{P}^-(n)}g\Big(x+\sum_{i\in I}u_i\Big)+\sum_{I\in\mathcal{P}^+(n)}f\Big(x+\sum_{i\in I}u_i\Big)\leq\sum_{I\in\mathcal{P}^+(n)}g\Big(x+\sum_{i\in I}u_i\Big)+\sum_{I\in\mathcal{P}^-(n)}f\Big(x+\sum_{i\in I}u_i\Big)\,.$$

> **Paper — Remark 7.13** (arXiv 2212.02371, LMCS 21(1:1), p. 1:58). Notice that if $f\leq g$ (still for the cone order relation of $P$, characterized by Lemma 7.12) then $f(x)\leq g(x)$ for all $x\in\mathcal{B}B$, but the converse is not true. As an example take $f(x)=x$ and $g(x)=1$, defining two stable functions (for $B=C=1$) which do not satisfy $f\leq_P g$ but are such that $f(x)\leq g(x)$ holds for all $x\in[0,1]$.

```coq
(* theories/stable/stablehom.v *)
Lemma sh_le_of_alt : precone_le f g.
Proof. by exists sh_diff; rewrite -sh_add_diff. Qed.
```

```coq
(* theories/stable/stablehom.v — Section StablehomLePointwise *)

(* Remark 7.13, the implication that does hold: the stable order is
   pointwise in [C].  Its converse is false — see the quote above. *)
Lemma sh_le_pointwise (f g : stablehom B C) :
  precone_le f g -> forall x : B, precone_le (sh_fun f x) (sh_fun g x).

(* Section StablehomDiff — the difference [g ⊖ f] is again stable, which
   is the [precone_le] witness [sh_le_of_alt] exhibits. *)
Definition sh_diff : stablehom B C.
Lemma sh_add_diff : sh_add f sh_diff = g.
```

### §7.2 norm (`sh_norm`, `sh_norm_ub`, `sh_norm_lub`, `sh_normh`, `sh_normt`, `sh_normp`, `sh_normz`)

The precone $B\Rightarrow_s C$ is normed by the operator norm $\lVert f\rVert=\sup_{\lVert x\rVert\leq 1}\lVert f(x)\rVert$, which exists because stable functions are bounded (`sh_normset_has_sup`); `sh_norm_ub` is the pointwise bound $\lVert f(x)\rVert\leq\lVert f\rVert$ on the unit ball and `sh_norm_lub` its least-upper-bound property, and the two together are the only interface the rest of the file uses. Of the four algebraic cone-norm axioms, (Normh) `sh_normh`, (Normt) `sh_normt` and (Normp) `sh_normp` follow from the corresponding axioms of $C$ pulled through `sh_norm_lub` / `sh_norm_ub` (with `sh_le_pointwise` supplying the order transfer for (Normp)); (Normz) `sh_normz` is the one that needs the carrier's $0$-extension field.

> **Paper — §7.2** (arXiv 2212.02371, LMCS 21(1:1), p. 1:58). We equip this precone $P$ with the norm $\lVert f\rVert=\sup_{x\in\mathcal{B}C}\lVert f(x)\rVert$ which is well defined by our assumptions that stable functions are bounded.

> **Difference.** The paper introduces the norm in one unnumbered sentence and leaves the verification of the cone axioms implicit ("*So $P$ is a cone …*"). The mechanisation names each axiom separately — `sh_normh`, `sh_normz`, `sh_normt`, `sh_normp` — and this exposes where the $0$-extension carrier of the §7.2 hom entry earns its keep: **(Normz)** is *not* provable from the supremum alone. From $\lVert f\rVert=0$ one gets $f(x)=0$ only for $\lVert x\rVert\leq 1$, which on the paper's ball-only carrier is already all of $f$; on the mechanisation's total carrier the off-ball values are pinned by `sh_offball`, and only then is $f$ the zero map.

```coq
(* theories/stable/stablehom.v — Section StablehomNorm *)

(* Paper §7.2: ‖f‖ = sup over the unit ball, well defined by boundedness. *)
Definition sh_norm (f : stablehom B C) : R.
Lemma sh_norm_ub (f : stablehom B C) (x : B) :
  cone_norm x <= 1 -> cone_norm (sh_fun f x) <= sh_norm f.
Lemma sh_norm_lub (f : stablehom B C) (M : R) : (* least upper bound *).

(* Section StablehomConeAxioms — (Normh) / (Normt) / (Normp) / (Normz). *)
Lemma sh_normh (r : {nonneg R}) f : sh_norm (sh_scale r f) = r%:num * sh_norm f.
Lemma sh_normt f g : sh_norm (sh_add f g) <= sh_norm f + sh_norm g.
Lemma sh_normp f g : precone_le f g -> sh_norm f <= sh_norm g.

(* (Normz) — the payoff of the canonical 0-extension carrier. *)
Lemma sh_normz f : sh_norm f = 0 -> f = sh_zero B C.
```

### Lem 7.14 (`sh_sup`, `sh_sup_ball_ub`, `sh_sup_ball_lub`, `sh_sup_ball_norm`)

Given a $\leq$-increasing chain $(f_n)$ of stable maps of norm $\leq 1$, the pointwise supremum `sh_sup_fun` $x\mapsto\sup_n f_n(x)$ is again bounded, totally monotonic, $\omega$-continuous and measurable, and is packaged as the `stablehom` `sh_sup`; `sh_sup_ball_ub`, `sh_sup_ball_lub` and `sh_sup_ball_norm` are its upper-bound, least-upper-bound and norm-$\leq 1$ properties. This is precisely the (Normc) axiom for $B\Rightarrow_s C$, and with the four norm axioms of the §7.2 norm entry it completes the `isCone` HB instance: $B\Rightarrow_s C$ is a `coneType R`.

> **Paper — Lemma 7.14** (arXiv 2212.02371, LMCS 21(1:1), p. 1:58). Let $(f_n\in\mathcal{B}P)_{n\in\mathbb{N}}$ be an increasing sequence (for the stable order). Then $f:\mathcal{B}C\to D$ defined by $f(x)=\sup_{n\in\mathbb{N}}f_n(x)$ is bounded, totally monotonic, $\omega$-continuous and measurable, that is, $f\in P$. This map $f$ is the lub of the $f_n$'s in $P$.

> **Difference.** The paper's least-upper-bound half is one sentence — "*The fact that $f$ is the lub of the $f_n$'s results from the fact that it is defined as a pointwise lub*" — because in the paper the stable order *is* read pointwise on the ball. In the mechanisation the precone order is the existential $f\leq g\iff\exists\delta,\ g=f+\delta$, so a lub proof must **produce a `stablehom` witness** for each gap. `sh_sup_ball_lub` obtains one without any general "difference of stable maps is stable" lemma: it re-runs the `sh_sup` construction on the difference chain $n\mapsto(f_{n+k}\ominus f_n)$, whose terms are handed over as `stablehom`s by the chain order itself, and closes with the Lemma 7.12 backward direction `sh_le_of_alt`.

```coq
(* theories/stable/stablehom.v — Section StablehomSupBall, Variables u : nat -> stablehom B C, uch, ub1 *)

(* Paper Lemma 7.14: the pointwise supremum, packaged as a stablehom. *)
Definition sh_sup : stablehom B C.

(* Section StablehomConeSup — the (Normc) universal properties. *)
Lemma sh_sup_ball_ub n : (* uₙ ≤ sh_sup *).
Lemma sh_sup_ball_lub (y : stablehom B C) :
  (forall m, precone_le (u m) y) -> precone_le (sh_sup uch ub1) y.
Lemma sh_sup_ball_norm : (* ‖sh_sup‖ ≤ 1 *).

(* With (Normh)/(Normz)/(Normt)/(Normp) and (Normc) above:
   [stablehom B C : coneType R] — the cone B ⇒ₛ C. *)
HB.instance Definition _ := @isCone.Build R (stablehom B C) (* sh_norm + the five axioms *).
```

### §7.2 icone (`sh_mcone_M`, `sh_int_fun`, `sh_int_car_pettis`, `sh_int_exists`)

The cone $B\Rightarrow_s C$ is given a measurability structure exactly as $C\multimap D$ was in §5.1: a test on $B\Rightarrow_s C$ over $Y$ is built (`sh_test`) from a unit-ball path $\gamma\in\mathsf{Path}(Y,B)$ and a $C$-test $m$ by $(\gamma\triangleright m)(r,f)=m(r,f(\gamma(r)))$, and `sh_mcone_M` is the set of all such tests; its three closure axioms `sh_mcone_M_comp` (reindexing), `sh_mcone_M_sep` (separation) and `sh_mcone_M_norm` (norm adherence) give the `isMCone` instance. Integrability is the pointwise Pettis integral `sh_int_fun`: for a measurable path $\eta$ into $B\Rightarrow_s C$ and $\mu\in\mathsf{FMeas}(Y')$, the map $x\mapsto\int_{r}\eta(r)(x)\,\mu(dr)$ is totally monotonic (`sh_int_fun_totmono`, from bilinearity of the integral), Scott-continuous on the ball (`sh_int_fun_scott`, monotone convergence) and path-preserving, hence a `stablehom`; `sh_int_car_pettis` is the Pettis equation $p(f)=\int_r p(\eta(r))\,\mu(dr)$ for it, and `sh_int_exists` is the resulting `isICone` witness. With all four HB instances registered, `stablehom B C` is an `iconeType Ar` — the object that Thm 7.32 uses as the cartesian-closed exponential.

> **Paper — §7.2** (arXiv 2212.02371, LMCS 21(1:1), pp. 1:58–1:59). So $P$ is a cone that we equip with a measurability structure $\mathcal{M}$ defined as in $C\multimap D$: a $p\in\mathcal{M}_X$ is a function $p=\gamma\triangleright m$ where $\gamma\in\mathsf{Path}(X,C)$ and $m\in\mathcal{M}^D_Y$, given by $$\gamma\triangleright m=\lambda(r,f)\in X\times P\cdot m(r,f(\gamma(r)))\,.$$ Then we check that $\mathcal{M}$ satisfies the required conditions exactly as we did for $C\multimap D$ in Section 5.1. We have defined a measurable cone $C\Rightarrow_s D$ that we prove now to be integrable.

> **Paper — §7.2** (arXiv 2212.02371, LMCS 21(1:1), p. 1:59). Let $X\in\mathbf{Ar}$ and $\eta\in\mathsf{Path}(X,C\Rightarrow_s D)$, and let $\mu\in\mathsf{FMeas}(X)$. We define a function $f:\mathcal{B}C\to D$ by $$f(x)=\int_{r\in X}\eta(r)(x)\,\mu(dr)\,.$$ This integral is well defined because, for each $x\in\mathcal{B}B$, the function $\lambda r\in X\cdot\eta(r)(x)$ is measurable and bounded since $\eta$ is a measurable path. The function $f$ is totally monotonic by bilinearity of integration, $\omega$-continuous by the monotone convergence theorem […] so that $f$ is the integral of $\eta$ over $\mu$, this shows that $C\Rightarrow_s D$ is an integrable cone.

> **Difference.** The paper's integrand is defined only on $\mathcal{B}C$; `sh_int_fun` is defined on all of $B$ by the usual `if cone_norm x <= 1 then … else 0` guard, which is what supplies the carrier's `sh_offball` field. As everywhere in the development, the `isICone` structure records *existence* of the integral (`sh_int_exists : is_path_integrable η µ`) rather than an integration operator; the value is recovered from the witness, and its uniqueness comes from (Mssep) — see the Def 4.3 entry.

```coq
(* theories/stable/stablehom.v — Section StablehomTest / Section StablehomMCone *)

(* Paper §7.2: the [γ ▷ m] test family, exactly as for [C ⊸ D]. *)
Definition sh_test : test_of Ar Y (stablehom B C).
Definition sh_mcone_M (Y : ar_obj Ar) : set (test_of Ar Y (stablehom B C)).
Lemma sh_mcone_M_comp : (* (Mscomp) — reindexing along ψ *).
Lemma sh_mcone_M_sep (f1 f2 : stablehom B C) : (* (Mssep) *).
Lemma sh_mcone_M_norm (f : stablehom B C) (eps : R) : (* (Msnorm) *).

HB.instance Definition _ := @isMCone.Build R Ar (stablehom B C) (* sh_mcone_M + its three axioms *).

(* Section StablehomICone / StablehomIntFun — the pointwise Pettis integral. *)
Definition sh_int_fun (x : B) : C.
Lemma sh_int_fun_totmono : is_totmono sh_int_fun.
Lemma sh_int_fun_scott : is_scott_continuous_unit sh_int_fun.
Lemma sh_int_car_pettis : path_integral_eq η µ sh_int_stablehom.
Lemma sh_int_exists : (* is_path_integrable η µ *).

HB.instance Definition _ := @isICone.Build R Ar (stablehom B C) (@sh_int_exists R Ar B C).
```

### §7.3 diff (`Delta_arg`, `Delta_pos`, `Delta_neg`, `Delta`, `Delta_E`, `Delta_neg_le_pos`)

The operator $\Delta$ that the whole of §7.3 is about is a named Rocq object, not an anonymous subterm of the `is_n_increasing` recursion. For a direction family $\overrightarrow{u}$ and a point $x$ of the local cone $B_{\overrightarrow{u}}$, `Delta_arg u x I` is the argument $\mathsf{lc\_val}\,x+\sum_{i\in I}u_i$; `Delta_pos` and `Delta_neg` are the two sign-split cone-sums $\sum_{I\in\mathcal{P}^{+}(n)}f(\ldots)$ and $\sum_{I\in\mathcal{P}^{-}(n)}f(\ldots)$; and `Delta` is their pointwise cone difference. Since the cone difference is only partial, `Delta` is defined by a case split on the order $\Delta^{-}\leq\Delta^{+}$ — the subtrahend witness where the order holds, the cone zero elsewhere — with `Delta_E` the defining equation $\Delta^{+}=\Delta^{-}+\Delta$ under that hypothesis. `Delta_neg_le_pos` is exactly what makes the first case the operative one on the ball: for totally monotonic $f$, $\Delta^{-}f(\overrightarrow{u})\leq\Delta^{+}f(\overrightarrow{u})$ there, which is an instance of Condition (7.1) transported through the local cone by `lc_step1`.

> **Paper — §7.3** (arXiv 2212.02371, LMCS 21(1:1), p. 1:60). Let $B$, $C$ be cones, $f:\mathcal{B}B\to C$ be a function, $n\in\mathbb{N}$ and $u_1,\dots,u_n\in B$ such that $\sum_{i=1}^n u_i\in\mathcal{B}B$; we define $$\Delta^{\epsilon}f(\overrightarrow{u}):\mathcal{B}B_{\overrightarrow{u}}\to C,\qquad x\mapsto\sum_{I\in\mathcal{P}^{\epsilon}(n)}f\Big(x+\sum_{i\in I}u_i\Big)$$ for $\epsilon\in\{-,+\}$ and if $f$ is totally monotonic we set $$\Delta f(\overrightarrow{u})=\Delta^{+}f(\overrightarrow{u})-\Delta^{-}f(\overrightarrow{u}):\mathcal{B}B_{\overrightarrow{u}}\to C,$$ the difference being computed pointwise. Notice that for $n=0$ (so that $\overrightarrow{u}=(\,)$) we have $\Delta f((\,))=f$ since $\mathcal{P}^{+}(0)=\{\emptyset\}$ and $\mathcal{P}^{-}(0)=\emptyset$.

> **Difference.** The paper writes $\Delta f(\overrightarrow{u})$ only "*if $f$ is totally monotonic*", so the operator's very definition carries a side condition. The mechanisation makes `Delta` **total** — the difference witness where $\Delta^{-}\leq\Delta^{+}$, the cone zero off that region — so that it can be quoted in the `is_n_increasing` `Fixpoint` and in every statement without dragging a totality proof through the recursion. Total monotonicity is then not part of the definition but a *lemma* about it (`Delta_neg_le_pos`), and every use on the ball goes through `Delta_E`. The subtrahend itself is extracted with `cid` from the existential in the precone order, which is why `Delta_E` — rather than a computation rule — is the equation the proofs rewrite with.

```coq
(* theories/stable/findiff.v — Section Delta, Variables R : realType, B C : coneType R, f : B -> C *)

(* The argument [lc_val x + Σ_{i∈I} uᵢ] of [f] for the index set [I]. *)
Definition Delta_arg (n : nat) (u : 'I_n -> B) (* x I *) : B.

(* Δ⁺ f u⃗ — sum over [Ppos n];  Δ⁻ f u⃗ — sum over [Pneg n]. *)
Definition Delta_pos (n : nat) (u : 'I_n -> B) (* x *) : C.
Definition Delta_neg (n : nat) (u : 'I_n -> B) (* x *) : C.

(* Δ f u⃗ — the pointwise cone difference Δ⁺ ⊖ Δ⁻, 0-extended off the
   region where the order Δ⁻ ≤ Δ⁺ holds. *)
Definition Delta (n : nat) (u : 'I_n -> B) (* x *) : C.

(* Defining equation: where Δ⁻ ≤ Δ⁺, one has Δ⁺ = Δ⁻ + Δ. *)
Lemma Delta_E (n : nat) (u : 'I_n -> B) (* x *) : (* Delta_pos = Delta_neg + Delta *).

(* Section DeltaWellDef — well-definedness on the ball is an instance of
   total monotonicity, transported into [B_u⃗] by [lc_step1]. *)
Lemma Delta_neg_le_pos (n : nat) (u : 'I_n -> B) (* Hs x *) :
  (* lc_norm x <= 1 -> precone_le (Delta_neg f u x) (Delta_pos f u x) *).

(* Lemma 7.17 (operator form): the Δ⁺ / Δ⁻ cons recurrences, splitting
   off a head direction u — the shape SD_cons mirrors on the B-side. *)
Lemma Delta_pos_recur : (* Δ⁺f(u::w⃗) x = Spos w (lc_val x + u) + Sneg w (lc_val x) *).
Lemma Delta_neg_recur : (* Δ⁻f(u::w⃗) x = Sneg w (lc_val x + u) + Spos w (lc_val x) *).
```

### Def 7.15 (`is_n_increasing`)

A function is *$n$-increasing* by induction on $n$: for $n=0$ it is simply increasing; for $n>0$ it is increasing and, for every direction $u\in\mathcal{B}\mathcal{M}B$, the single-step difference $\Delta f(u):\mathcal{B}\mathcal{M}B_u\to\mathcal{M}C$ (mapping $x$ to $f(x+u)-f(x)$) is $(n-1)$-increasing from the local cone $B_u$ to $C$. This inductive definition — a `Fixpoint` on $n$ whose recursive call changes the source cone from $B$ to the local cone of $u$ — is the backbone of the whole finite-difference development.

> **Paper — Definition 7.15** (arXiv 2212.02371). Let $f:\mathcal{B}\mathcal{M}B\to\mathcal{M}C$ be a function and $n\in\mathbb{N}$. $f$ is *$n$-increasing from $B$ to $C$* if either $n=0$ and $f$ is increasing, or $n>0$, $f$ is increasing and, for all $u\in\mathcal{B}\mathcal{M}B$, the function $\Delta f(u):\mathcal{B}\mathcal{M}B_u\to\mathcal{M}C$ (which maps $x$ to $f(x+u)-f(x)$) is $(n-1)$-increasing from $B_u$ to $C$.

```coq
(* theories/stable/findiff.v *)
Fixpoint is_n_increasing (n : nat) (R : realType) (B C : coneType R)
    (f : B -> C) {struct n} : Prop :=
  match n with
  | 0 => is_increasing f
  | n'.+1 => is_increasing f /\
      forall (u : B) (Hu : cone_norm
        (\big[precone_add/precone_zero]_(i : 'I_1) (fun=> u) i) < 1),
        @is_n_increasing n' R (lc_coneType Hu) C (Delta f (fun=> u))
  end.
```

### Lem 7.16 (`is_n_increasing_Delta`)

If $f$ is $n$-increasing for every $n$, then so is each single-step difference $\Delta f(u)$: this is exactly the second conjunct of `is_n_increasing` at arity $n+1$, read off directly.

> **Paper — Lemma 7.16** (arXiv 2212.02371, `lemma:fdiff-inf-increasing`). Let $f\in\mathcal{B}\mathcal{M}B\to\mathcal{M}C$ be a function which is $n$-increasing for all $n\in\mathbb{N}$. Then for all $u\in\mathcal{B}\mathcal{M}B$, the function $\Delta f(u):\mathcal{B}\mathcal{M}B_u\to\mathcal{M}C$ is $n$-increasing for all $n\in\mathbb{N}$.

```coq
(* theories/stable/findiff.v *)
Lemma is_n_increasing_Delta (R : realType) (B C : coneType R) (f : B -> C) :
  (forall n, is_n_increasing n f) ->
  forall (u : B) (Hu : cone_norm
     (\big[precone_add/precone_zero]_(i : 'I_1) (fun=> u) i) < 1) (n : nat),
    @is_n_increasing n R (lc_coneType Hu) C (Delta f (fun=> u)).
```

### Lem 7.18 (`totmono_Delta1`)

The single-step difference $\Delta f(u)$ of a totally monotonic $f$ is again totally monotonic on the local cone $B_u$; this is the key inductive step feeding Theorem 7.19 (distinct from the multi-direction `totmono_Delta` of the 7.20–7.25 machinery).

> **Paper — Lemma 7.18** (arXiv 2212.02371, `lemma:fdiff-tot-mono`). If a function $f\in\mathcal{B}\mathcal{M}B\to\mathcal{M}C$ is totally monotonic, then for each $u\in\mathcal{B}\mathcal{M}B$, the function $\Delta f(u):\mathcal{B}\mathcal{M}B_u\to\mathcal{M}C$ is totally monotonic.

> **Difference.** The paper's $u$ ranges over the closed ball $\mathcal{B}\mathcal{M}B$; the section header below carries `Hsu : ‖su‖ < 1`, the **strict** bound. That is not an extra hypothesis of this lemma: `lc_coneType` is only defined at strict-interior points, so the bound is the local cone $B_u$'s own precondition. See the strict-interior Difference under Lem 7.1 for why the whole of `local_cone.v` is stated that way.

```coq
(* theories/stable/findiff.v — Section Lemma718: R, B C, f, u, Hsu : ‖su‖ < 1, Bu := lc_coneType Hsu, oneu := fun _ : 'I_1 => u *)
Lemma totmono_Delta1 (Hf : is_totmono f) : @is_totmono R Bu C (Delta f oneu).
```

### Thm 7.19 (`totmono_is_n_increasing`, `is_n_increasing_totmono`)

Total monotonicity is equivalent to being $n$-increasing for every $n$ (the inductive characterization via iterated first differences over local cones). The two lemmas give the forward and converse directions.

> **Paper — Theorem 7.19** (arXiv 2212.02371, `th:induct-total-nonotone`). A function $f\in\mathcal{B}\underline{B}\to\underline{C}$ is totally monotonic iff it is $n$-increasing for all $n\in\mathbb{N}$.

> **Difference.** The converse `is_n_increasing_totmono` carries an extra `is_scott_continuous_unit` hypothesis, and is proved on the closed unit ball. *Why:* the finite-difference recovery of the parity inequality is established $\omega$-continuously on the ball. The $n$-increasing hypothesis alone already delivers Condition (7.1) on the **open** ball — that is `conv_strict` — and $\omega$-continuity is used only to pass from there to the closed ball by taking a supremum, which is exactly the step the paper does not have to make.

```coq
(* theories/stable/findiff.v *)
Lemma totmono_is_n_increasing (n : nat) (R : realType) (B C : coneType R)
    (f : B -> C) : is_totmono f -> is_n_increasing n f.

(* The strict-interior converse: Condition (7.1) on the OPEN ball,
   from n-increasingness alone — no ω-continuity needed. *)
Lemma conv_strict (R : realType) (B C : coneType R) (f : B -> C) :
  (forall k, is_n_increasing k f) ->
  (* strictly-interior configurations satisfy the Pneg ≤ Ppos order *).

(* Variables: R B C f. *)
Lemma is_n_increasing_totmono :
  (forall k, is_n_increasing k f) -> is_scott_continuous_unit f ->
  is_totmono f.
```

### Lem 7.20–7.25 (`SD`, `SD_Delta`, `SD_cons`, `SD_add`, `SD_perm`, `SD_mono_full`, finite-difference / SnB machinery)

The signed finite-difference machinery driving Thm 7.19 and the §7.3 closure properties. `totmono_Delta` packages Lemma 7.20 — for totally monotonic $f$, the positive, negative, and full iterated differences $\Delta^+f(\overrightarrow{u})$, $\Delta^-f(\overrightarrow{u})$, $\Delta f(\overrightarrow{u})$ are totally monotonic on the residual ball — while `SnB_increasing` packages Lemma 7.25, that the global iterated-difference map $(x,\overrightarrow{u})\mapsto\Delta f(\overrightarrow{u})(x)$ is increasing on the auxiliary cone $\mathsf{S}^n B$.

`SD` is the *B-side* difference engine: the same signed difference read at a bare $B$-centre rather than at a point of the local cone $B_{\overrightarrow{u}}$, with `SD_Delta` the bridge $\Delta f(\overrightarrow{u})(x)=\mathsf{SD}\,\overrightarrow{u}\,(\mathsf{lc\_val}\,x)$ between the two readings. On the $B$-side the paper's recurrences become the two Lemma 7.22 identities `SD_cons` (shifting the centre by a new head direction) and `SD_add` (splitting a direction $u+v$), whose telescope at general arity is Lemma 7.23, `SD_diag` and its head-peeled form `SD_723`. Lemma 7.20's $\Delta^{\pm}$ clauses come from `totmono_shift_le` (each dominated shift $g_{s_I}(x)=f(\mathsf{lc\_val}\,x+s_I)$ is totally monotonic) plus `totmono_bigP` (a finite cone-sum of totally monotonic maps is totally monotonic), and the $\Delta$ clause is `totmono_Delta`, obtained from the $(n+m)$-configuration of $f$'s own total monotonicity. Lemma 7.25 (`SnB_increasing`) is then read off `SD_mono_full`, joint monotonicity of the difference in the centre and in every direction, itself the composite of `SD_mono_centre` (centre) and the permutation symmetry `SD_perm` (directions).

> **Paper — Lemma 7.20** (arXiv 2212.02371, `lemma:fdiff-tot-mon`). Let $f:\mathcal{B}\underline{B}\to\underline{C}$ be totally monotonic and $\overrightarrow{u}\in\underline{B}^n$ be such that $\sum_{i=1}^n u_i\in\mathcal{B}\underline{B}$. Then the functions $\Delta^+ f(\overrightarrow{u}),\Delta^- f(\overrightarrow{u}),\Delta f(\overrightarrow{u}):\mathcal{B}\underline{B_{\overrightarrow{u}}}\to\underline{C}$ are totally monotonic.

> **Paper — Lemma 7.25** (arXiv 2212.02371, `lemma:fdiff-glob-increasing`). If $f:\mathcal{B}\underline{B}\to\underline{C}$ is totally monotonic, the map $(x,\overrightarrow{u})\to\Delta f(\overrightarrow{u})(x)$ is increasing $\mathcal{B}\mathsf{S}^n B\to\underline{C}$.

```coq
(* theories/stable/compose.v *)

(* [totmono_Delta]: the finite-difference [Δf(u⃗) := SDpos f − SDneg f]
   on the unit ball, packaging Δε / Δ for ε ∈ {+, −}. *)
Lemma totmono_Delta (n : nat) (u : 'I_n -> B)
    (Hs : (* sum bound on u *)) :
  (* totmono of f gives totmono of Δf(u⃗) on the residual ball *).

(* theories/stable/findiff.v — [SnB] is a CONE, not a predicate:
   the carrier is the family type ['I_n.+1 -> B] (the centre [g ord0]
   together with the [n] directions), with pointwise [0]/[+]/[*:] and
   pointwise order, normed by the norm of the total sum
   [snb_norm g := cone_norm (snb_sum g)].  Its unit ball is exactly the
   paper's configuration set [‖x + Σᵢ uᵢ‖ ≤ 1]. *)
Definition SnB (R : realType) (B : coneType R) (n : nat) : coneType R :=
  snb_car B n.

(* Lemma 7.25 ([theories/stable/compose.v]): [(x,u⃗) ↦ Δf(u⃗)(x)],
   read off the family as centre [g ord0] and tail directions. *)
Definition SnB_diff (g : SnB B n) : C :=
  SD f (fun i => g (lift ord0 i)) (g ord0).
Lemma SnB_increasing : is_increasing SnB_diff.
```

> **Paper — Lemma 7.22** (arXiv 2212.02371, LMCS 21(1:1), p. 1:62). Let $f:\mathcal{B}B\to C$ be a totally monotonic function. Let $n\in\mathbb{N}$, $u,v\in\mathcal{B}B$ and $\overrightarrow{u}\in\mathcal{B}B^n$, and assume that $u+v+\sum_{i=1}^n u_i\in\mathcal{B}B$. Then for each $x\in\mathcal{B}B_{\overrightarrow{u}}$ we have $$\Delta f(\overrightarrow{u})(x+u)=\Delta f(\overrightarrow{u})(x)+\Delta f(u,\overrightarrow{u})(x)$$ $$\Delta f(u+v,\overrightarrow{u})(x)=\Delta f(u,\overrightarrow{u})(x)+\Delta f(v,\overrightarrow{u})(x+u)\,.$$

> **Paper — Lemma 7.23** (arXiv 2212.02371, LMCS 21(1:1), p. 1:63). Let $f:\mathcal{B}B\to C$ be totally monotonic. Let $n\in\mathbb{N}$, $u\in B$ and $\overrightarrow{u},\overrightarrow{v}\in B^n$, and assume that $u+\sum_{i=1}^n(u_i+v_i)\in\mathcal{B}B$. Then for each $x\in\mathcal{B}B_{u,\overrightarrow{u},\overrightarrow{v}}$ we have $$\Delta f(\overrightarrow{u}+\overrightarrow{v})(x+u)=\Delta f(\overrightarrow{u})(x)+\Delta f(u,\overrightarrow{u}+\overrightarrow{v})(x)+\Delta f(v_1,u_2+v_2,\dots,u_n+v_n)(x+u_1)+\Delta f(u_1,v_2,u_3+v_3,\dots,u_n+v_n)(x+u_2)+\cdots+\Delta f(u_1,\dots,u_{n-1},v_n)(x+u_n)\,.$$

> **Difference.** Two departures, both about *where* differences are read. (1) The paper proves Lemma 7.25 in one line — "*Follows easily from Theorem 7.19*" — i.e. through the $n$-increasing characterisation and hence through $\omega$-continuity. The mechanisation proves it **directly and with no recourse to $\omega$-continuity**, as `SD_mono_full`: monotonicity in the centre (`SD_mono_centre`) composed with monotonicity in the directions, which is obtained from `SD_perm`, the symmetry of $\mathsf{SD}$ under permuting the direction family. (2) The paper's difference operators live on local cones, so the composition argument of Lemma 7.26 differentiates at a local cone of a local cone and silently uses the cast $(B_{u_0})_{\overrightarrow{w}}\cong B_{u_0,\overrightarrow{w}}$. The `SD` engine reads every difference on bare $B$-centres, free of local-cone packaging, so the reindexing identities (`SD_perm`) and the telescopes (`SD_diag`, `SD_723`) are equalities between $C$-elements and the cast is never written down. `SD_Delta` is the single place where the two readings are related.

```coq
(* theories/stable/findiff.v — Section SDelta, Variables R, B C : coneType R, f : B -> C *)

(* The B-side cone difference [Spos ⊖ Sneg] at a bare centre [xb]. *)
Definition SD (n : nat) (u : 'I_n -> B) (xb : B) : C.

(* The bridge: the operator form [Delta] is [SD] at the centre [lc_val x]. *)
Lemma SD_Delta (n : nat) (u : 'I_n -> B) (* x *) : (* Delta f u x = SD u (lc_val x) *).

(* Lemma 7.22, both identities, on the B-side. *)
Lemma SD_cons (Hf : is_totmono f) (n : nat) (u : B) (w : 'I_n -> B) (xb : B) (* Hc *) :
  SD w (xb + u) = SD w xb + SD (vcons u w) xb.
Lemma SD_add (Hf : is_totmono f) (n : nat) (u v : B) (w : 'I_n -> B) (xb : B) (* Hc *) :
  SD (vcons (u + v) w) xb = SD (vcons u w) xb + SD (vcons v w) (xb + u).
```

```coq
(* theories/stable/compose.v — the reindexing / monotonicity / telescope family *)

(* Permutation symmetry of the direction family. *)
Lemma SD_perm (n : nat) (s : 'S_n) (u : 'I_n -> B) (xb : B) :
  SD f (u \o s) xb = SD f u xb.

(* Lemma 7.25: monotone in the centre, then jointly in centre + directions. *)
Lemma SD_mono_centre (n : nat) (u : 'I_n -> B) (xb d : B) : (* SD u xb ≤ SD u (xb + d) *).
Lemma SD_mono_full (n : nat) (u u' : 'I_n.+1 -> B) (xb xb' : B) : (* joint monotonicity *).

(* Lemma 7.23 at general arity: the diagonal split and its head-peeled telescope. *)
Lemma SD_diag (xb : B) (* Hc *) : (* SD f (u + v) xb = SD f u xb + Σₖ … *).
Lemma SD_723 (u0 xb : B) (* Hc *) : (* the shifted-centre telescope *).

(* Lemma 7.20, the Δ⁺/Δ⁻ clauses and the Δ clause. *)
Lemma totmono_shift_le (g : B -> C) (S s : B) (* Hs *) : (* the dominated shift is totmono *).
Lemma totmono_bigP (P Q : coneType R) (T : finType) (A : {set T}) : (* a finite \sumP of totmono maps *).
```

### Lem 7.21 (`Delta_le`, `SD_le`)

For totally monotonic $f$, the iterated finite difference $\Delta f(\overrightarrow{u})(x)$ is bounded above by the value of $f$ at the summed point $x+\sum_i u_i$. `Delta_le` is the operator form on the local-cone unit ball; it is read off from the B-side bound `SD_le` (the same inequality stated for the raw signed-difference operator $\mathsf{SD}$) via `SD_Delta`.

> **Paper — Lemma 7.21** (arXiv 2212.02371, `lemma:fdiff-upper`). Let $f:\mathcal{B}\mathcal{M}B\to\mathcal{M}C$ be totally monotonic. Then for each $\overrightarrow{u}\in\mathcal{M}B^n$ such that $\sum_{i=1}^n u_i\in\mathcal{B}\mathcal{M}B$ and $x\in\mathcal{M}B_{\overrightarrow{u}}$ we have $\Delta f(\overrightarrow{u})(x)\leq f\big(x+\sum_{i=1}^n u_i\big)$.

```coq
(* theories/stable/findiff.v — B-side form *)
Lemma SD_le (Hf : is_totmono f) (n : nat) (u : 'I_n -> B) (xb : B) :
  cone_norm (xb + \big[precone_add/precone_zero]_(i : 'I_n) u i) <= 1 ->
  SD u xb <=p f (xb + \big[precone_add/precone_zero]_(i : 'I_n) u i).

(* Section Lemma721: R, B C, f, Hf : is_totmono f — operator form *)
Lemma Delta_le (n : nat) (u : 'I_n -> B)
    (Hs : cone_norm (\big[precone_add/precone_zero]_(i : 'I_n) u i) < 1)
    (x : local_cone (\big[precone_add/precone_zero]_(i : 'I_n) u i))
    (Hx : lc_norm x <= 1) :
  Delta f u x <=p
  f (lc_val x + \big[precone_add/precone_zero]_(i : 'I_n) u i).
```

### Lem 7.26 (`ninc_kfun`, `totmono_comp`)

The Faà-di-Bruno-style composition lemma — the deepest result of §7.3. Given totally monotonic $f,h_1,\dots,h_n:\mathcal{B}\mathcal{M}B\to\mathcal{M}C$ and $g:\mathcal{B}\mathcal{M}C\to\mathcal{M}D$ with $f+\sum_i h_i$ staying in the unit ball, the composite $k(x)=\Delta g(h_1 x,\dots,h_n x)(f x)$ is totally monotonic. The main statement `ninc_kfun` establishes, by a generic $p$-induction, that the B-side composite `kfun g f h⃗` is $p$-increasing for every source cone, arity and admissible data (which with `is_n_increasing_totmono` yields total monotonicity of $k$); its $n=0$ corollary `totmono_comp` — $g\circ f=\mathsf{kfun}\,g\,f\,()$ — drives Theorem 7.30.

> **Paper — Lemma 7.26** (arXiv 2212.02371, `lemma:fdiff-comp`). Let $n\in\mathbb{N}$, $f,h_1,\dots,h_n:\mathcal{B}\mathcal{M}B\to\mathcal{M}C$ and $g:\mathcal{B}\mathcal{M}C\to\mathcal{M}D$ be totally monotonic functions such that $\forall x\in\mathcal{B}\mathcal{M}B\ f(x)+\sum_{i=1}^n h_i(x)\in\mathcal{B}\mathcal{M}C$. Then the function $k:\mathcal{B}\mathcal{M}B\to\mathcal{M}D$ defined by $k(x)=\Delta g(h_1(x),\dots,h_n(x))(f(x))$ is totally monotonic.

> **Difference — defeating the nested-cone cast.** The paper's proof of 7.26 differentiates the composite at a local cone *of a local cone*, $(B_{u_0})_{\vec w}$, and silently uses the cast $(B_{u_0})_{\vec w}\cong B_{u_0,\vec w}$ to line that up with the $(1+n)$-ary difference. Formalising that transport is painful, so the mechanisation is arranged so that **the cast never has to be written down**, by two moves. *(i) The difference engine is B-side.* `SD` reads every signed difference at a bare $B$-centre, free of local-cone packaging, and carries the reindexing identities `SD_cons` / `SD_add` / `SD_perm` and the concatenation engine (§ Lem 7.20–7.25); `SD_Delta` is the only bridge back to the $B_{\vec u}$ reading, and it is applied once at the end. *(ii) The induction is quantified over all source cones at once.* `ninc_kfun` is a $p$-induction on `is_n_increasing` — a predicate that recurses into $B_u$ — whose statement re-quantifies `forall (B : coneType R)` *inside* the induction (note the shadowing binder in the snippet below). At the $p+1$ step the goal sits at source $B_u$, and it is discharged by instantiating the very same inductive hypothesis at source $B_u$; the local-cone summands therefore feed the hypothesis directly and no explicit transport is ever constructed. This generic-source shape is why `ninc_kfun` reads as "for every source cone" rather than as the paper's single-cone statement, and it is the insight that crosses the §7.3 "mountain".

```coq
(* theories/stable/compose.v — Section vars: R, B C D, g : C -> D, Hg : is_totmono g *)
Definition kfun (n : nat) (f : B -> C) (h : 'I_n -> (B -> C)) : B -> D :=
  fun x => SD g (fun i => h i x) (f x).

(* The p-induction is quantified over the SOURCE cone (shadowing the
   section's B), so its own hypothesis applies at the local cone B_u —
   the (B_u)_w ≅ B_{u,w} cast is never written.  See the Difference. *)
Lemma ninc_kfun (p : nat) :
  forall (B : coneType R) (n : nat) (f : B -> C) (h : 'I_n -> (B -> C)),
  is_totmono f -> (forall i, is_totmono (h i)) ->
  (forall y : B, cone_norm y <= 1 ->
     cone_norm (f y + \big[precone_add/precone_zero]_(i : 'I_n) h i y) <= 1) ->
  is_n_increasing p (kfun g f h).

(* The p = 0 base clause: kfun is increasing, because SD g is jointly
   increasing in centre and directions (SD_mono_full, Lem 7.25). *)
Lemma kfun_increasing : (* is_increasing (kfun f h) *).

(* The p+1 step, B-side: the single-step difference of the composite
   splits as the paper's (n+1)-term Lemma-7.23 sum of SD g's at shifted
   centres — each of which is again a kfun, so the induction hypothesis
   applies at source B_u with no transport. *)
Lemma dB_kfun : (* dB (kfun f h) u x = SD g (vcons ...) (f x) + Σ ... *).

(* n = 0 corollary: g ∘ f is totally monotonic. *)
Lemma totmono_comp (f : B -> C) (g : C -> D)
    (Hf : is_stable f) (Hg : is_stable g)
    (Hfb : forall x, cone_norm x <= 1 -> cone_norm (f x) <= 1) :
  is_totmono (fun x => g (f x)).
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

Stable and measurable functions of norm $\le 1$ are closed under composition (the well-definedness of the category $\mathbf{SCones}$). `stable_comp` handles the stable part and `meas_stable_comp` the measurable-path-preservation part. `is_stable` bundles four clauses, and each is closed separately before they are repackaged: total monotonicity by `totmono_comp` (Lem 7.26 at $n=0$), $\omega$-continuity on the unit ball by `scott_comp`, the norm bound by `bounded_comp`, and — on the measurable side — path preservation by `meas_path_comp`, which reassociates $(g\circ f)\circ\gamma$ as $g\circ(f\circ\gamma)$ and uses $f$'s bound to keep the inner image $f\circ\gamma$ inside $\mathcal{B}\mathcal{M}C$ where $g$'s path preservation applies.

> **Paper — Theorem 7.30** (arXiv 2212.02371). If $f\in\mathbf{SCones}(B,C)$ and $g\in\mathbf{SCones}(C,D)$ then $g\mathrel{\circ}f\in\mathbf{SCones}(B,D)$.

```coq
(* theories/stable/compose.v — Section CompClosure: R, B C D *)
(* The clause-by-clause closure lemmas stable_comp repackages. *)
Lemma scott_comp : (* ω-continuity on the unit ball composes *).
Lemma bounded_comp : (* the norm bound composes *).
Lemma meas_path_comp : (* measurable-path preservation composes *).

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

### Cat 7 (`scones_hom`, `sc_norm`, `scones_id`, `scones_comp`, `scones_compA`)

$\mathbf{SCones}$ has the integrable cones as objects; a morphism $B\to C$ is the record `scones_hom`, bundling a function with a proof that it is measurable stable (`sc_meas_stable`), the operator-norm bound $\lVert f\rVert\leq 1$ (`sc_norm_le1`, for the norm `sc_norm` with its `sc_norm_ub` / `sc_norm_lub` characterisation) and the canonical $0$-extension field `sc_offball`. All three proof fields are `Prop`, so `scones_hom_eq` reduces equality to equality of the underlying functions. The identity `scones_id` and the composition `scones_comp` — well defined by Thm 7.30, with the norm bound supplied pointwise by `sc_image_ball` — satisfy the three category laws `scones_compIl`, `scones_compIr` and `scones_compA` as plain Leibniz equalities. This is the category in which Thm 7.32's products and cartesian-closed structure, and the functor $\mathsf{Der}$ of Lem 7.31, live.

> **Paper — §7.4** (arXiv 2212.02371, LMCS 21(1:1), p. 1:65). Let $\mathbf{SCones}(B,C)$ be the set of all stable and measurable functions from $B$ to $C$ whose norm is $\leq 1$. […] So we have defined a category $\mathbf{SCones}$ whose objects are the integrable cones, and the morphisms are the stable and measurable functions.

> **Difference — morphisms as $0$-extended maps.** The paper's morphisms are functions $f:\mathcal{B}B\to C$ on the unit ball, equal when they agree there. The mechanisation keeps a total carrier plus the off-ball field `sc_offball` (the same device as the internal hom's `sh_offball`, see §7.2 hom), so that equality of morphisms is Leibniz equality. The apparent obstruction is that for a **non-linear** $g$ one has $g(0)\neq 0$ in general, so a bare composite $g\circ f$ does not vanish off the ball. The resolution is to define the identity, composition, $\mathsf{Der}$ and the tupling as *"compose, then re-extend by $0$ off the ball"*: the clamp `sc_clamp` sets the value to $0$ outside $\mathcal{B}B$, and it preserves measurable stability because that predicate is unit-ball-determined (`meas_stable_eq_on_ball`: a map agreeing on $\mathcal{B}B$ with a stable map is stable), while the norm bound $\lVert f\rVert\leq 1$ supplies the ball-preservation `sc_image_ball` that the bare composite needs. *Consequence:* every category law, the functoriality of $\mathsf{Der}$ and the product universal property below hold as plain equalities, each proved by a case split on $\lVert x\rVert\leq 1$ — no setoid and no quotient anywhere in §7.

```coq
(* theories/stable/scones_cat.v — Section SconesNorm / Section SconesHom,
   Variables R : realType, Ar : MeasSubcat R, B C : ICone.type Ar *)

(* The operator norm on bare functions, and its two characterising bounds. *)
Definition sc_norm (f : B -> C) : R.
Lemma sc_norm_ub (f : B -> C) (Hf : is_meas_stable f) (x : B) : (* ‖f x‖ ≤ sc_norm f *).
Lemma sc_norm_lub (f : B -> C) (M : R) : (* least upper bound *).

Record scones_hom : Type := MkSconesHom { (* sc_fun / sc_meas_stable / sc_norm_le1 / sc_offball *) }.

Lemma scones_hom_eq (f g : scones_hom) :
  (forall x, sc_fun f x = sc_fun g x) -> f = g.

(* Section SconesClamp — the 0-re-extension and the two facts that make it work. *)
Definition sc_clamp f : B -> C.
Lemma meas_stable_eq_on_ball f g : (* agreeing on B_B with a stable map ⇒ stable *).
Lemma sc_image_ball (f : scones_hom B C) (x : B) :
  cone_norm x <= 1 -> cone_norm (sc_fun f x) <= 1.

(* Section SconesCat — identity, composition and the three category laws. *)
Definition scones_id : scones_hom B B.
Definition scones_comp (g : scones_hom C D) (f : scones_hom B C) : scones_hom B D.
Lemma scones_compIl (B C : ICone.type Ar) (f : scones_hom B C) :
  scones_comp (scones_id C) f = f.
Lemma scones_compIr (B C : ICone.type Ar) (f : scones_hom B C) :
  scones_comp f (scones_id B) = f.
Lemma scones_compA (B1 B2 B3 B4 : ICone.type Ar) (* h g f *) : (* associativity *).
```

### Lem 7.31 (`linear_totmono`, `linear_stable`, `ders`, `ders_id`, `ders_comp`, `ders_faithful`)

Every linear (integrable-cone) morphism is stable, so the integrable-cone morphisms embed into the stable/measurable ones — this is the forgetful (dereliction) functor $\mathsf{Der}:\mathbf{ICones}\to\mathbf{SCones}$, acting as the identity on objects and morphisms. The core is `linear_totmono` (linearity implies total monotonicity), packaged with boundedness and $\omega$-continuity into `linear_stable`, and realized as the inclusion map `ders` on `icones_hom` (the underlying linear function $0$-extended off the unit ball).

`linear_stable` has exactly three ingredients: `linear_totmono` above, the norm bound, and `linear_scott_unit` — the §7.0 bridge `linear_scott_of_omega` specialised to unit-ball input, which is what turns an $\mathbf{ICones}$ morphism's $\omega$-continuity into the `is_scott_continuous_unit` that `is_stable` demands. `icones_meas_stable` packages a linear `icones_hom` as a measurable stable map, and `ders` clamps it. That $\mathsf{Der}$ really is a *functor* is `ders_id` and `ders_comp`; that it is *faithful* is `ders_faithful`, which recovers equality of the linear maps everywhere from equality of the clamped ones on the ball (by homogeneity: rescale $x$ into the ball by $(\lVert x\rVert+1)^{-1}$ and scale back). $\mathsf{Der}$ is **not** full — paper Examples 2.4 and 7.9 exhibit non-linear totally monotonic functions — and nothing in the development claims otherwise.

> **Paper — Lemma 7.31 and §7.4** (arXiv 2212.02371, LMCS 21(1:1), p. 1:65). $\mathbf{ICones}(B,C)\subseteq\mathbf{SCones}(B,C)$. *Proof.* Indeed linearity clearly implies total monotonicity. So we have a functor $\mathsf{Der}_s:\mathbf{ICones}\to\mathbf{SCones}$ which acts as the identity on objects and morphisms. We can consider this functor as a forgetful functor since it forgets linearity, whence its name: in LL the purpose of the dereliction rules allows to forget the linearity of morphisms. The functor $\mathsf{Der}_s$ is obviously faithful but of course not full: see Examples 2.4 and 7.9 which provide nonlinear totally monotonic functions.

> **Difference.** The paper's functor is *literally* the identity on morphisms, because its stable maps are already functions on the unit ball. In the mechanisation `ders` is the identity followed by the $0$-clamp `sc_clamp` (see the Cat 7 note), so "acts as the identity on morphisms" becomes the two proved equations `ders_id` / `ders_comp` rather than a definitional triviality — and correspondingly `ders_faithful` needs the $(\lVert x\rVert+1)$-rescaling argument to get from agreement on the ball back to equality of the linear maps. Note also that the paper's one-line proof, "*linearity clearly implies total monotonicity*", is `linear_totmono`, an induction on the arity of (7.1).

The arity induction behind that one line has two ingredients, both in `scones_cat.v`. *Counting:* `card_Ppos_Pneg` shows $\lvert\mathcal{P}^+(n{+}1)\rvert=\lvert\mathcal{P}^-(n{+}1)\rvert$ — each family splits into an `injI0`-image and an `injI`-image of the lower-arity families (Lem 7.4) and the two contributions are swapped between the signs — from which `big_Pneg_le_Ppos` gives that a *constant* cone-sum over $\mathcal{P}^-(n)$ is $\le$ the one over $\mathcal{P}^+(n)$ (equal for $n>0$ by `big_const`; the negative sum is $0$ at $n=0$). *Shifting:* `Spos_lin_shift` / `Sneg_lin_shift` say that for a linear $f$, moving the centre by $e$ adds exactly the constant sum $\sum f(e)$ to each signed sum — `linearD` splits the image and `sumP_add` distributes the split through the `bigop`. Together, the $n{+}1$ instance of (7.1) reduces to the $n$ instance plus a comparison of two constant sums, which is where `big_Pneg_le_Ppos` closes it.

```coq
(* theories/stable/scones_cat.v — Section LinearTotmono *)
(* Counting: the two sign-split families are equinumerous at arity n+1,
   so a CONSTANT Pneg-sum is dominated by the Ppos-sum. *)
Lemma card_Ppos_Pneg (n : nat) : #|Ppos n.+1| = #|Pneg n.+1|.
Lemma big_Pneg_le_Ppos : (* Σ_(I in Pneg n) c <=p Σ_(I in Ppos n) c *).

(* Section LinearShift: for a LINEAR f, shifting the centre by e adds
   the constant sum Σ f e to each signed sum. *)
Lemma Spos_lin_shift : (* Spos f n w (xb + e) = Spos f n w xb + Σ_(I in Ppos n) f e *).
Lemma Sneg_lin_shift : (* Sneg f n w (xb + e) = Sneg f n w xb + Σ_(I in Pneg n) f e *).

(* theories/stable/scones_cat.v — Section LinearTotmonoMain: R, B C, f : B -> C, Hf : is_linear f *)
Lemma linear_totmono : is_totmono f.

(* Section LinearStable: adds Hcont : is_omega_continuous f and the norm bound. *)
Lemma linear_stable : is_stable f.

(* Paper Lemma 7.31: the inclusion ICones(B,C) → SCones(B,C). *)
Definition ders (B C : ICone.type Ar) (h : icones_hom Ar B C) :
    scones_hom B C :=
  MkSconesHom (sc_clamp (Lfun h)) (ders_meas_stable h) (ders_norm_le1 h)
    (sc_clamp_offball_field _).
```

```coq
(* theories/stable/scones_cat.v — Section LinearStable / Section IconesMeasStable *)

(* The §7.0 bridge specialised to unit-ball input — the ω-continuity
   ingredient [is_stable] needs. *)
Lemma linear_scott_unit : is_scott_continuous_unit f.

(* A linear ICones morphism, packaged as a measurable stable map. *)
Lemma icones_meas_stable (h : icones_hom Ar B C) : (* is_meas_stable (Lfun h) *).

(* Section Ders — functoriality and faithfulness of Der. *)
Lemma ders_id (B : ICone.type Ar) : ders (icones_id Ar B) = scones_id B.
Lemma ders_comp (B C D : ICone.type Ar)
    (g : icones_hom Ar C D) (f : icones_hom Ar B C) :
  ders (icones_comp g f) = scones_comp (ders g) (ders f).
Lemma ders_faithful (B C : ICone.type Ar) (f g : icones_hom Ar B C) :
  ders f = ders g -> f = g.
```

### §7.4 products (`scones_proj`, `scones_tuple`, `scones_tuple_proj`, `scones_tuple_unique`)

The products half of Theorem 7.32, at the paper's full $I$-indexed generality (the Thm 7.32 entry below documents the *binary* CCC record). The $\mathbf{ICones}$ product $\mathop{\&}_{i\in I}B_i$ serves unchanged, with projections $\mathsf{scones\_proj}\,i:=\mathsf{Der}(\mathrm{pr}_i)$; the tupling $\langle f_i\rangle:y\mapsto(f_i\,y)_i$ is `scones_tuple`. Measurable stability of the tuple reduces componentwise through two lemmas: `cones_prod_val_big`, that projection commutes with the product cone-sum (so each sign-split sum of the (7.1) inequality is computed factorwise), and `cones_prod_le_compI`, the backward direction of the componentwise cone order (so the product inequality follows from its factors). The universal property is a pair of Leibniz equalities — `scones_tuple_proj` for the factorisation $\mathrm{pr}_i\circ\langle f_j\rangle=f_i$ and `scones_tuple_unique` for uniqueness of the mediating morphism — so $\mathop{\&}_{i\in I}B_i$ is the categorical product in $\mathbf{SCones}$.

> **Paper — Theorem 7.32, products half** (arXiv 2212.02371, LMCS 21(1:1), pp. 1:65–1:66). If $(B_i)_{i\in I}$ is a family of integrable cones, we have already defined $B=\mathop{\&}_{i\in I}B_i$ which is the categorical product of the $B_i$'s in $\mathbf{ICones}$ (when equipped with the projections $\mathrm{pr}_i\in\mathbf{ICones}(B,B_i)$). So $\mathsf{Der}_s(\mathrm{pr}_i)\in\mathbf{SCones}(B,B_i)$ for each $i\in I$. Let $(f_i\in\mathbf{SCones}(C,B_i))_{i\in I}$, we define $f:\mathcal{B}C\to\mathcal{B}B$ by $f(x)=(f_i(x))_{i\in I}$ which is well defined by our assumption that $\forall i\in I\ \lVert f_i\rVert\leq 1$. Then $f$ is easily seen to be stable because all the operations of $B$, as well as its cone order relation, are defined componentwise. Measurability of $f$ is proven as in the proof of Theorem 4.16. This shows that $B$ is the categorical product of the $B_i$'s in $\mathbf{SCones}$.

> **Difference.** The paper's "*well defined by our assumption that $\forall i\in I\ \lVert f_i\rVert\leq 1$*" is a real proof obligation in the mechanisation: a point of the $\mathit{Type}$-indexed product carrier must carry a **uniform** bound $\exists M,\forall i,\lVert x_i\rVert\leq M$, and for an arbitrary index type $I$ this holds for the tuple only on the unit ball, where $\lVert f_i\,y\rVert\leq\lVert f_i\rVert\leq 1$ gives $M:=1$ (`scones_tuple_bd`). The tuple is therefore built with a *point-level* clamp — the family $(f_i\,y)_i$ for $\lVert y\rVert\leq 1$, the product zero off the ball — which is exactly the $0$-extension of the Cat 7 note; the record-level `sc_clamp` then supplies the `sc_offball` field. Because of it, both universal-property statements are plain Leibniz equalities rather than equalities-on-the-ball.

```coq
(* theories/stable/scones_cat.v — Section SconesProducts,
   Variables R, Ar, I : Type, B : I -> ICone.type Ar, Q : ICone.type Ar,
   f : forall i, scones_hom Q (B i);  P := icones_prod B *)

(* The i-th SCones projection is Der of the i-th ICones projection. *)
Definition scones_proj (i : I) : scones_hom P (B i) := ders (icones_proj i).

(* The two componentwise reductions the tuple's stability rests on. *)
Lemma cones_prod_le_compI (x y : P) :
  (forall i, cones_prod_val x i <=p cones_prod_val y i) -> x <=p y.
Lemma cones_prod_val_big (T : finType) (A : {set T}) (h : T -> P) (i : I) :
  (* projection commutes with the product cone-sum *).

(* The uniform bound M = 1 that a point of the product carrier requires. *)
Lemma scones_tuple_bd (y : Q) : (* exists M, forall i, ‖clamp (f i) y‖ ≤ M *).

(* Paper Theorem 7.32 (tupling) and its universal property. *)
Definition scones_tuple : scones_hom Q P.
Lemma scones_tuple_proj (i : I) : scones_comp (scones_proj i) scones_tuple = f i.
Lemma scones_tuple_unique (g : scones_hom Q P) :
  (forall i, scones_comp (scones_proj i) g = f i) -> g = scones_tuple.
```

### Thm 7.32 (`SCones_CCC`, `SCones_ccc`)

The category $\mathbf{SCones}$ of integrable cones and stable/measurable functions has all products and is cartesian closed, with internal hom the cone $\mathbf{SCones}(B,C)$ and evaluation morphism $\mathsf{Ev}(f,x)=f(x)$. `SCones_CCC` is the record packaging the product and exponential data with their $\beta$/$\eta$ laws; `SCones_ccc` is the witness assembled from `sprod`, `Ev`, `curry`, etc.

Four steps carry the exponential. `sprod_pair_norm_le1` is the product side: a pairing of two unit-ball points is in the unit ball of `sprod`, which is what lets `Ev` and `curry` compute at all. `curry_app h z` is the *section* $x\mapsto h(z,x)$ packaged as an element of the internal hom `stablehom B C`, $0$-extended off $\mathcal{B}D$ and off $\mathcal{B}B$ by `sc_clamp` (the Cat 7 device again). That `curry h` is itself stable needs its (7.1) inequality **in the cone** `stablehom B C`, which is `curry_totmono_step`: through `sh_le_of_alt` (Lem 7.12 backwards) it reduces to a pointwise comparison plus the alternating condition, and both are instances of total monotonicity of $h$ over `sprod D B` with the $D$-increments $(w_i,0)$ interleaved with the $B$-increments $(0,u_j)$. That interleaving is why the arity-indexed (7.1) of Def 7.5 is not directly usable: the index family is a product of two `'I_n`s rather than a single one, so `gen_totmono` first generalises total monotonicity from `'I_n` to an arbitrary `finType` index — the parity is transported along `enum_rank`, whose image has the same cardinality. `curry_beta` and `curry_eta` are then the $\beta$ and $\eta$ laws, each proved by `scones_hom_eq` and a case split on whether the argument is in the ball.

> **Paper — Theorem 7.32** (arXiv 2212.02371). The category $\mathbf{SCones}$ has all products and is cartesian closed.

```coq
(* theories/stable/scones_ccc.v — the exponential's four steps *)

(* Total monotonicity over an arbitrary finType index family, by
   transporting the parity along enum_rank. *)
Lemma gen_totmono : (* the (7.1) order for a T-indexed family, T : finType *).

(* Products: a pairing of two unit-ball points is in the unit ball. *)
Lemma sprod_pair_norm_le1 (x : X) (y : Y) :
  cone_norm x <= 1 -> cone_norm y <= 1 ->
  cone_norm (sprod_pair x y) <= 1.

(* The section x ↦ h(z,x) as an element of the internal hom. *)
Definition curry_app (z : D) : stablehom B C.

(* Its (7.1) inequality IN THE CONE stablehom B C — the heart of
   "curry h is stable" (via sh_le_of_alt and gen_totmono). *)
Lemma curry_totmono_step : (* the Pneg ≤ Ppos order for curry_app *).

(* The two exponential laws. *)
Lemma curry_beta (h : scones_hom SDB C) :
  scones_comp (Ev B C) (pairing h) = h.
Lemma curry_eta (g : scones_hom D H) :
  curry (scones_comp (Ev B C) (gpair g)) = g.
```

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
| LL $!$ | The linear-exponential comonad $! : \mathbf{ICones} \to \mathbf{ICones}$, obtained as $! = \mathsf{E}\circ\mathsf{Der}$ where $\mathsf{E}$ is the left adjoint of $\mathsf{Der}$ (existing by the special adjoint functor theorem). | `Bang`, `nl`, `lin`, `lin_beta`, `lin_unique` (the adjunction data) — `theories/exp/exp_adjunction.v`; `Bang_comonad` — `theories/exp/bang.v` |
| §9 Theta | The adjunction bijection $\Theta_{B,C}:\mathbf{ICones}({!B},C)\to\mathbf{SCones}(B,C)$, $h\mapsto\mathsf{Der}(h)\circ\mathsf{nl}_B$, inverse to $\mathsf{lin}$; promotion $x^!=\mathsf{nl}_B(x)$ and its unit-ball bound; and the pointwise reading $(\Theta h)(x)=h(x^!)$. | `Theta`, `ThetaK`, `linK`, `prom`, `prom_ball`, `Theta_prom` — `theories/exp/bang.v` |
| Comonad | $(!, \mathsf{der}, \mathsf{dig})$ is a comonad with the standard counit / coassociativity, satisfying $\mathsf{der}_B(x^!)=x$ and $\mathsf{dig}_B(x^!)=x^{!!}$. | `der`, `dig`, `der_prom`, `dig_prom`, the comonad laws — `theories/exp/bang.v` |
| Comonad laws | The three comonad equations and the two functor laws, each proved by reduction to promoted points. | `comonad_counitL`, `comonad_counitR`, `comonad_coassoc`, `bang_fmap_id`, `bang_fmap_comp` — `theories/exp/bang.v` |
| Lem 9.2 | Two linear maps ${!B_1}\otimes\cdots\otimes{!B_n}\to C$ agreeing on every promoted pure tensor $x_1^!\otimes\cdots\otimes x_n^!$ (for $x_i\in\mathcal{B}\underline{B_i}$) are equal. | `tens_excl_charact` (the $n=2$ case characterising the binary Seely iso), with `tens_excl_charact3` / `tens_excl_charact3l` the $n=3$ coherence instances — `theories/exp/seely.v` |
| Lem 9.2 n=1 | The base case: two linear maps ${!B}\to C$ agreeing on every promoted point $x^!$ are equal — the workhorse every comonad and Seely law reduces to, also available at the `linhom_car` level. | `bang_ext` — `theories/exp/bang.v`; `bang_ext_linhom` — `theories/exp/seely.v`; `linhom_icones`, `linhom_iconesE` — `theories/homs/tensor_hom_iso.v` |
| Lem 9.3 | The exponential functor on a promoted point: $({!f})(x^!)=f(x)^!$. | `bang_fmap_prom` (the computation behind `bang_fmap_id` / `bang_fmap_comp` functoriality and `Coalg_coassoc`) — `theories/exp/bang.v` |
| Lem 9.4 | The natural iso $(B \Rightarrow (C \multimap D)) \simeq (C \multimap (B \Rightarrow D))$ ("swap a stable outer and a linear inner"). | `stab_lin_swap` (a fully spelled-out `icones_iso`; paper gives the map + "pattern seen many times", no proof) — `theories/exp/stab_lin_swap.v` |
| Lem 9.4 naturality | The stable/linear swap is natural in all three slots — pre-composition in $B$, pre-composition in $C$, post-composition in $D$ (the slot Thm 9.5 consumes). | `stab_lin_swap_nat1`, `stab_lin_swap_nat2`, `stab_lin_swap_nat3` — `theories/exp/stab_lin_swap.v` |
| Thm 9.5 | $(\mathbf{ICones}, \otimes, 1, !)$ is a **Seely category** (i.e. has the Seely isos $\mathsf{m}^2 : {!B_1} \otimes {!B_2} \simeq {!(B_1 \mathrel{\&} B_2)}$ and $\mathsf{m}^0 : 1 \simeq {!\top}$, and the comonad / SMC coherence). | `Seely2`, `Seely2E`, `Seely2_natural`, `Seely0`, `Seely0E`, the full `SeelyCategory` record + the witness `ICones_Seely` — `theories/exp/seely.v` |
| Thm 9.5 comult | The comultiplication coherence square the paper draws explicitly: $!\langle{!\pi_1},{!\pi_2}\rangle\circ\mathsf{dig}\circ\mathsf{m}^2=\mathsf{m}^2\circ(\mathsf{dig}\otimes\mathsf{dig})$, over the $\mathrel{\&}$-projection tuple. | `seely_comult`, `bang_proj_tuple`, `bang_proj_tupleE`, `sproj1`, `sproj2` — `theories/exp/seely.v` |
| Thm 9.5 coherence | The strong-monoidal coherence of $({!},\mathsf{m}^2,\mathsf{m}^0)$ against $\alpha/\sigma/\lambda/\rho$, plus the counit compatibility (the binary square in projected form). | `seely_assoc`, `seely_braid`, `seely_lunit`, `seely_runit`, `seely_der_unit`, `seely_der1`, `seely_der2`, `tens_excl_unitL`, `tens_excl_unitR` — `theories/exp/seely.v`; `Stop_mor` — `theories/exp/seely_defs.v` |
| Thm 9.7 | For each $X \in \mathbf{Ar}$, $\mathsf{FMeas}(X)$ is a $!$-coalgebra (with structure map $\mathsf{h}_X(\mu) = \int_{r\in X} (\boldsymbol\delta^X(r))^! \,\mu(dr)$); the assignment $X \mapsto \mathsf{FMeas}(X)$ is a functor into $\mathbf{ICones}^!$. | `Coalg`, `Coalg_dirac`, `dirac_dense`, `FMeas_coalgebra`, `FMeas_fmap` — `theories/exp/coalgebra.v` |
| Thm 9.7 functor | $\mathsf{FMeas}(\phi)$ is a morphism of $!$-coalgebras, and coalgebra morphisms contain the identities and are closed under composition — the content of "$\mathsf{FMeas}$ is a functor $\mathbf{Ar}\to\mathbf{ICones}^!$". | `is_coalg_mor`, `coalg_mor_id`, `coalg_mor_comp`, `FMeas_fmap_dirac`, `FMeas_fmap_is_coalg_mor` — `theories/exp/coalgebra.v` |
| Sect 9.2 | Fixpoint combinator $\mathcal{Y}$ on the cartesian closed $\mathbf{SCones}$. | `Yfix`, `Yfix_fix` (the paper's CCC construction) — `theories/stable/fixpoint.v` |

### Linear exponential `!` (`Bang`, `nl`, `lin`, `lin_beta`, `lin_unique`)

The linear exponential ${!B} = \mathsf{E}(B)$ is the object part of the left adjoint $\mathsf{E}$ of $\mathsf{Der} : \mathbf{ICones}\to\mathbf{SCones}$. Its universal property is the *universal nonlinear map* $\mathsf{nl}_B \in \mathbf{SCones}(B, {!B})$ (the unit of the adjunction): every stable map $f\in\mathbf{SCones}(B,C)$ factors as $f = \mathsf{der}(\phi)\circ\mathsf{nl}_B$ for a *unique* linear $\phi\in\mathbf{ICones}({!B},C)$, written $\mathsf{lin}\,f = \Theta^{-1}_{B,C}(f)$. Writing $x^! = \mathsf{nl}_B(x)$ for $x$ in the unit ball, this gives $f(x) = (\mathsf{lin}\,f)(x^!)$.

> **Paper — §9** (arXiv 2212.02371, `sec:lin-nonlin-adj`). Let $\mathsf{E} : \mathbf{SCones}\to\mathbf{ICones}$ be the left adjoint of $\mathsf{Der}$, which exists by Theorem 4.19, and $\Theta_{B,C} : \mathbf{ICones}(\mathsf{E}B,C)\to\mathbf{SCones}(B,\mathsf{Der}\,C)=\mathbf{SCones}(B,C)$ the associated natural bijection (remember $\mathsf{Der}\,C=C$). Let $\mathsf{nl}_B=\Theta_{B,\mathsf{E}B}(\mathsf{Id}_{\mathsf{E}B})\in\mathbf{SCones}(B,{!B})$ be the unit of the adjunction, which is the "universal nonlinear map" on $B$ in the sense that for each integrable cone $C$ and each $f\in\mathbf{SCones}(B,C)$ one has $f=\phi\circ\mathsf{nl}_B$ for a unique $\phi\in\mathbf{ICones}({!B},C)$, namely $\phi=\Theta^{-1}_{B,C}(f)$. So that for $h\in\mathbf{ICones}({!B},C)$ one has $\Theta_{B,C}(h)=h\circ\mathsf{nl}_B$. For each $x\in\mathcal{B}\underline{B}$ we set $x^!=\mathsf{nl}_B(x)\in\mathcal{B}\underline{{!B}}$ so that, for $f\in\mathbf{SCones}(B,C)$, we have $f(x)=\Theta^{-1}_{B,C}(f)(x^!)$.

```coq
(* theories/exp/exp_adjunction.v — Section ExpInterface,
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

### §9 Theta (`Theta`, `ThetaK`, `linK`, `prom`, `prom_ball`, `Theta_prom`)

The paper's hom-bijection $\Theta$ and its promoted points are Rocq objects, not just notation. `Theta h := ders h ∘ nl_B` is the forward direction $\mathbf{ICones}({!B},C)\to\mathbf{SCones}(B,C)$; the two cancellations are `ThetaK` ($\Theta(\mathsf{lin}\,f)=f$, i.e. the existence half `lin_beta`) and `linK` ($\mathsf{lin}(\Theta\,h)=h$, i.e. the uniqueness half `lin_unique` instantiated at $f:=\Theta\,h$), so $\Theta$ and $\mathsf{lin}$ are mutually inverse. Promotion is `prom B x = nl_B(x)`, written $x^!$; since $\mathsf{nl}_B$ is a $\mathbf{SCones}$-morphism and hence norm-$\leq 1$, promotion keeps the unit ball (`prom_ball`). The bridge between the two is `Theta_prom`: for $\lVert x\rVert\leq 1$, $(\Theta\,h)(x)=h(x^!)$ — this is what turns any equation between linear maps out of ${!B}$ into a computation on promoted points.

> **Paper — §9** (arXiv 2212.02371, `sec:lin-nonlin-adj`). Let $\Theta_{B,C}:\mathbf{ICones}(\mathsf{E}B,C)\to\mathbf{SCones}(B,\mathsf{Der}\,C)=\mathbf{SCones}(B,C)$ [be] the associated natural bijection (remember $\mathsf{Der}\,C=C$). […] So that for $h\in\mathbf{ICones}({!B},C)$ one has $\Theta_{B,C}(h)=h\circ\mathsf{nl}_B$. For each $x\in\mathcal{B}\underline{B}$ we set $x^!=\mathsf{nl}_B(x)\in\mathcal{B}\underline{{!B}}$.

> **Difference.** A $\mathbf{SCones}$-morphism is a stable map *clamped to $0$ off the unit ball*, so the identity $(\Theta\,h)(x)=h(x^!)$ is stated on the ball only — `Theta_prom` carries the hypothesis `cone_norm x <= 1`, and the off-ball case is not an omission but the definitional $0$ on both sides. *Why:* the 0-extension is how `scones_hom` makes a map defined on a ball into a total function; every promoted-point argument in this chapter therefore splits into an on-ball computation and an off-ball `sc_clamp_offball` step (see `bang_ext`).

```coq
(* theories/exp/bang.v — Section Bang, Variables (R : realType) (Ar : MeasSubcat R) *)

Definition Theta.

Lemma ThetaK.

Lemma linK.

Definition prom.

Lemma prom_ball.

Lemma Theta_prom.
```

### Comonad (`der`, `dig`, `Comonad`, `Bang_comonad`)

The comonad induced on $\mathbf{ICones}$ by the linear-non-linear adjunction has counit $\mathsf{der}_B \in \mathbf{ICones}({!B}, B)$ (dereliction, characterised by $\mathsf{der}_B(x^!) = x$) and comultiplication $\mathsf{dig}_B = \mathsf{E}(\mathsf{nl}_B) \in \mathbf{ICones}({!B}, {!!B})$ (digging, characterised by $\mathsf{dig}_B(x^!) = x^{!!}$). The `Comonad` record bundles the endofunctor $!$ together with `der`, `dig` and the functor / comonad laws; `Bang_comonad` is the canonical, axiom-free witness on $\mathbf{ICones}$.

> **Paper — §9** (arXiv 2212.02371, `sec:lin-nonlin-adj`). We use $(!, \mathsf{der}, \mathsf{dig})$ for the induced comonad on $\mathbf{ICones}$ whose Kleisli category is (equivalent to) $\mathbf{SCones}$. The counit $\mathsf{der}_B\in\mathbf{ICones}({!B},B)$ of the comonad ${!}\_$ is also the counit of the adjunction; it satisfies $\forall x\in\mathcal{B}\underline{B}\ \ \mathsf{der}_B(x^!)=x$. The comultiplication $\mathsf{dig}_B\in\mathbf{ICones}({!B},{!!B})$ is defined by $\mathsf{dig}_B=\mathsf{E}(\mathsf{nl}_B)$ so that $\forall x\in\mathcal{B}\underline{B}\ \ \mathsf{dig}_B(x^!)=x^{!!}$.

> **Difference.** The paper obtains $!$, $\mathsf{der}$, $\mathsf{dig}$ from the abstract left adjoint $\mathsf{E}$; the formalization takes the same route but bundles the comonad as an explicit record `Comonad` (endofunctor + counit + comultiplication + laws) so that the Seely and coalgebra layers can quantify over it. The Kleisli-equivalence discussion is kept informal in the paper and is not part of the mechanised bundle.

```coq
(* theories/exp/bang.v *)

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

### Comonad laws (`comonad_counitL`, `comonad_counitR`, `comonad_coassoc`, `bang_fmap_id`, `bang_fmap_comp`)

The laws the `Comonad` record above lists as fields are individually proved lemmas, so each can be inspected — and `Print Assumptions`-ed — on its own. The two counit laws are $\mathsf{der}_{!B}\circ\mathsf{dig}_B=\mathrm{id}_{!B}$ (`comonad_counitL`) and ${!(\mathsf{der}_B)}\circ\mathsf{dig}_B=\mathrm{id}_{!B}$ (`comonad_counitR`); coassociativity is $\mathsf{dig}_{!B}\circ\mathsf{dig}_B={!(\mathsf{dig}_B)}\circ\mathsf{dig}_B$ (`comonad_coassoc`). Functoriality of $!$ is `bang_fmap_id` and `bang_fmap_comp`. Every one of the five is proved by the same recipe: apply `bang_ext` to reduce to a promoted point $x^!$, then compute with `der_prom`, `dig_prom` and `bang_fmap_prom` (Lem 9.3) — e.g. the left counit is $\mathsf{der}_{!B}(x^{!!})=x^!$ and coassociativity is $x^{!!!}$ on both sides.

> **Paper — §9** (arXiv 2212.02371, `sec:lin-nonlin-adj`). The counit $\mathsf{der}_B\in\mathbf{ICones}({!B},B)$ of the comonad ${!}\_$ is also the counit of the adjunction; it satisfies $\forall x\in\mathcal{B}\underline{B}\ \ \mathsf{der}_B(x^!)=x$. The comultiplication $\mathsf{dig}_B\in\mathbf{ICones}({!B},{!!B})$ is defined by $\mathsf{dig}_B=\mathsf{E}(\mathsf{nl}_B)$ so that $\forall x\in\mathcal{B}\underline{B}\ \ \mathsf{dig}_B(x^!)=x^{!!}$.

```coq
(* theories/exp/bang.v — Section Bang, Variables (R : realType) (Ar : MeasSubcat R) *)

Lemma bang_fmap_id.

Lemma bang_fmap_comp.

Lemma comonad_counitL.

Lemma comonad_counitR.

Lemma comonad_coassoc.
```

### Lem 9.2 (`tens_excl_charact`)

Promoted pure tensors are *jointly separating* for linear maps out of a tensor of exponentials: two maps $f,g\in\mathbf{ICones}({!B_1}\otimes\cdots\otimes{!B_n},C)$ that agree on every $x_1^!\otimes\cdots\otimes x_n^!$ (with each $x_i$ in the unit ball) are equal. This is what pins down the Seely isos: an equation on promoted pure tensors fully characterises a map. The formalization provides the $n=2$ case `tens_excl_charact` (used for the binary Seely iso $\mathsf{m}^2$) together with the two $n=3$ instances `tens_excl_charact3` (right-associated $!A\otimes(!B\otimes!C)$) and `tens_excl_charact3l` (left-associated $(!A\otimes!B)\otimes!C$) needed by the monoidal-coherence proofs.

> **Paper — Lemma 9.2** (arXiv 2212.02371, `lemma:tens-excl-equal-charact`). Let $n\geq 1$, let $B_1,\dots,B_n,C$ be objects of $\mathbf{ICones}$ and $f$ and $g$ be elements of $\mathbf{ICones}({!B_1}\otimes\cdots\otimes{!B_n},C)$ such that $f(x_1^!\otimes\cdots\otimes x_n^!)=g(x_1^!\otimes\cdots\otimes x_n^!)$ for all $(x_i\in\mathcal{B}\underline{B_i})_{i=1}^n$. Then $f=g$.

> **Difference.** The paper states the lemma for general $n$ (by induction). The mechanisation instantiates the $n=2$ case actually used to characterise the binary Seely iso, and the two $n=3$ cases (right- and left-associated) needed by the monoidal-functor associativity coherence; the $n=3$ proofs are the paper's induction step unfolded once, reducing to the $n=2$ case.

```coq
(* theories/exp/seely.v *)

Lemma tens_excl_charact (B1 B2 C : ICone.type Ar)
    (f g : icones_hom Ar (Bang Ar B1 ⊗ Bang Ar B2) C) :
  (forall (x1 : B1) (x2 : B2),
     cone_norm x1 <= 1 -> cone_norm x2 <= 1 ->
     Lfun f (x1! ⊗p x2!) = Lfun g (x1! ⊗p x2!)) ->
  f = g.

Lemma tens_excl_charact3 (A B C C0 : ICone.type Ar)
    (f g : icones_hom Ar (Bang Ar A ⊗ (Bang Ar B ⊗ Bang Ar C)) C0) :
  (forall (x : A) (y : B) (z : C),
     cone_norm x <= 1 -> cone_norm y <= 1 -> cone_norm z <= 1 ->
     Lfun f (x! ⊗p (y! ⊗p z!)) = Lfun g (x! ⊗p (y! ⊗p z!))) ->
  f = g.

Lemma tens_excl_charact3l (A B C C0 : ICone.type Ar)
    (f g : icones_hom Ar ((Bang Ar A ⊗ Bang Ar B) ⊗ Bang Ar C) C0) :
  (forall (x : A) (y : B) (z : C),
     cone_norm x <= 1 -> cone_norm y <= 1 -> cone_norm z <= 1 ->
     Lfun f ((x! ⊗p y!) ⊗p z!) = Lfun g ((x! ⊗p y!) ⊗p z!)) ->
  f = g.
```

### Lem 9.2 n=1 (`bang_ext`, `bang_ext_linhom`, `linhom_icones`, `linhom_iconesE`)

The $n=1$ instance of Lem 9.2 is the base case the $n=2$ and $n=3$ instances above reduce to, and the workhorse of the whole chapter: two linear maps $f,g:{!B}\to C$ that agree on every promoted point $x^!$ (for $\lVert x\rVert\leq 1$) are equal (`bang_ext`). Its proof is the hom-bijection: it suffices that $\Theta f=\Theta g$, since then $f=\mathsf{lin}(\Theta f)=\mathsf{lin}(\Theta g)=g$ by `linK`; the two stable maps agree on the ball by `Theta_prom` and the hypothesis, and off the ball both are $0$. The induction step of Lem 9.2 needs the same principle one level down, where the curried image is a `linhom_car` *element* rather than a morphism: `bang_ext_linhom` states it for norm-$\leq 1$ elements $\varphi,\psi:{!B}\multimap C$, via the element$\to$morphism bridge `linhom_icones` (a `linhom_car` of operator norm $\leq 1$ *is* an `icones_hom`, the per-point bound being `linhom_norm_apply_le` at $K=1$) with its computation law `linhom_iconesE`.

> **Paper — Lemma 9.2** (arXiv 2212.02371, `lemma:tens-excl-equal-charact`). Let $n\geq 1$, let $B_1,\dots,B_n,C$ be objects of $\mathbf{ICones}$ and $f$ and $g$ be elements of $\mathbf{ICones}({!B_1}\otimes\cdots\otimes{!B_n},C)$ such that $f(x_1^!\otimes\cdots\otimes x_n^!)=g(x_1^!\otimes\cdots\otimes x_n^!)$ for all $(x_i\in\mathcal{B}\underline{B_i})_{i=1}^n$. Then $f=g$.

> **Difference.** The paper's induction is over $n$; the mechanisation gives the base case ($n=1$, `bang_ext`) as a standalone lemma and unfolds the step once for $n=2$ and twice for $n=3$ (see the Lem 9.2 entry above). *Why:* the base case is used on its own everywhere — every comonad law, `bang_fmap_prom`'s consumers and the Seely coherence all discharge through `bang_ext` — and the step needs an extra ingredient the paper leaves implicit, namely that the *value* of a curried morphism at a promoted point is a `linhom_car` element and must be brought back to a morphism (`linhom_icones`) before the base case applies. `linhom_icones` / `linhom_iconesE` are defined in `theories/homs/tensor_hom_iso.v` and re-exported under the same names by `theories/exp/seely.v`.

```coq
(* theories/exp/bang.v *)
Lemma bang_ext.
```

```coq
(* theories/homs/tensor_hom_iso.v *)

Definition linhom_icones.

Lemma linhom_iconesE.
```

```coq
(* theories/exp/seely.v *)
Lemma bang_ext_linhom.
```

### Lem 9.3 (`bang_fmap_prom`)

The exponential functor $!$ commutes with promotion on unit-ball points: for a linear map $f\in\mathbf{ICones}(B,C)$ and $x\in\mathcal{B}\underline{B}$, we have $({!f})(x^!)=f(x)^!$. This single computation is the engine behind functoriality of $!$ (`bang_fmap_id`, `bang_fmap_comp`), the naturality squares `der_nat` / `dig_nat`, the Seely naturality `Seely2_natural`, and the coalgebra coassociativity `Coalg_coassoc`.

> **Paper — Lemma 9.3** (arXiv 2212.02371, `lemma:excl-fun-prom`). Let $f\in\mathbf{ICones}(B,C)$ and $x\in\mathcal{B}\underline{B}$. We have $({!f})(x^!)=f(x)^!$.

```coq
(* theories/exp/bang.v *)

Lemma bang_fmap_prom (B C : ICone.type Ar) (f : icones_hom Ar B C) (x : B) :
  cone_norm x <= 1 -> Lfun (bang_fmap f) x! = prom (Lfun f x).
```

### Lem 9.4 (`stab_lin_swap`)

The *stable/linear swap* isomorphism exchanges a stable outer argument and a linear inner one: $(B \Rightarrow (C \multimap D)) \simeq (C \multimap (B \Rightarrow D))$, natural in $B$, $C$, $D$, sending $f$ to $\boldsymbol\lambda y\in\underline{C}\cdot\boldsymbol\lambda x\in\mathcal{B}\underline{B}\cdot f(x,y)$. It is the key ingredient in deriving the binary Seely iso. The paper gives only the map and calls the verification "a pattern seen many times"; the formalization spells out both directions and the cancellation proofs as a full `icones_iso`.

> **Paper — Lemma 9.4** (arXiv 2212.02371, `lemma:stab-lin-swap`). Let $B,C,D$ be integrable cones. There is an isomorphism in $\mathbf{ICones}$ from $L(B,C,D)=(B\Rightarrow(C\multimap D))$ to $R(B,C,D)=(C\multimap(B\Rightarrow D))$ which is natural in $B$, $C$ and $D$. The natural isomorphism maps $f\in\underline{B\Rightarrow(C\multimap D)}$ to $\boldsymbol\lambda y\in\underline{C}\cdot\boldsymbol\lambda x\in\mathcal{B}\underline{B}\cdot f(x,y)$.

```coq
(* theories/exp/stab_lin_swap.v — Section variables B C D : ICone.type Ar *)

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

### Lem 9.4 naturality (`stab_lin_swap_nat1`, `stab_lin_swap_nat2`, `stab_lin_swap_nat3`)

The paper asserts that the stable/linear swap is natural in $B$, $C$ and $D$; the development proves the three squares, one per slot, each as a pointwise identity between the two ways of transporting an $f\in B\Rightarrow_s(C\multimap D)$. In $B$ (`stab_lin_swap_nat1`) the action of $k:B'\multimap B$ is precomposition `sh_prec k` on the left-hand side and postcomposition by `sh_prec k` inside the linear hom on the right; both read $f(k\,x')(y)$, and off the unit ball of $B'$ both are $0$ by the clamp. In $C$ (`stab_lin_swap_nat2`) the action of $k:C'\multimap C$ is `sh_postc (linhom_pre_icones k)` against `linhom_prec k`; both read $f(x)(k\,y')$. In $D$ (`stab_lin_swap_nat3`) the action of $h:D\multimap D'$ is `sh_postc (linhom_post_icones h)` against `sh_postc h`; both read $h(f(x)(y))$. The third slot is the one the binary Seely iso consumes.

> **Paper — Lemma 9.4** (arXiv 2212.02371, `lemma:stab-lin-swap`). Let $B,C,D$ be integrable cones. There is an isomorphism in $\mathbf{ICones}$ from $L(B,C,D)=(B\Rightarrow(C\multimap D))$ to $R(B,C,D)=(C\multimap(B\Rightarrow D))$ which is natural in $B$, $C$ and $D$.

> **Difference.** The paper states naturality as a property of a natural transformation between functors; the mechanisation states it *pointwise* — three equations between the values of the two composites at an argument — rather than as three commuting squares of `icones_hom`s. *Why:* the functorial actions in each slot are themselves defined pointwise (`sh_prec`, `sh_postc`, `linhom_prec`, `linhom_pre_icones` / `linhom_post_icones`), and the consumers in `seely.v` use the equations at a point; the morphism-level squares would add a layer of extensionality lemmas with no extra content.

```coq
(* theories/exp/stab_lin_swap.v — Section StabLinSwapNat,
   Variables (R : realType) (Ar : MeasSubcat R) *)

Lemma stab_lin_swap_nat1.

Lemma stab_lin_swap_nat2.

Lemma stab_lin_swap_nat3.
```

### Thm 9.5 (`Seely2`, `Seely2E`, `Seely2_natural`, `Seely0`, `Seely0E`, `SeelyCategory`, `ICones_Seely`)

Equipped with the strong monoidal comonad $!$, the SMCC $\mathbf{ICones}$ is a **Seely category**. Concretely, there are natural isos $\mathsf{m}^2_{B_1,B_2} : {!B_1}\otimes{!B_2}\simeq{!(B_1\mathrel{\&}B_2)}$ characterised by $\mathsf{m}^2_{B_1,B_2}(x_1^!\otimes x_2^!)=\langle x_1,x_2\rangle^!$, and $\mathsf{m}^0 : 1\simeq{!\top}$ characterised by $\mathsf{m}^0(t)=t\cdot 0^!$, together with the required comonad / SMC coherence diagrams. The `SeelyCategory` record bundles the SMCC, the comonad, the two Seely isos with their characterisations and naturality, and the coherence witnesses; `ICones_Seely` is the canonical, axiom-free instance.

> **Paper — Theorem 9.5** (arXiv 2212.02371). Equipped with the strong monoidal comonad $!$, the category $\mathbf{ICones}$ is a Seely category in the sense of Melliès.

> **Paper — §9** (arXiv 2212.02371, `sec:lin-nonlin-adj`). There is a natural isomorphism $\mathsf{m}^2_{B_1,B_2}$ in $\mathbf{ICones}({!B_1}\otimes{!B_2},{!(B_1\mathrel{\&}B_2)})$ which satisfies $\mathsf{m}^2_{B_1,B_2}(x_1^!\otimes x_2^!)=\langle x_1,x_2\rangle^!$ (this equation fully characterizes $\mathsf{m}^2_{B_1,B_2}$ by Lemma 9.2). Similarly we define an iso $\mathsf{m}^0\in\mathbf{ICones}(1,{!\top})$ such that $\mathsf{m}^0(t)=t\,0^!$ for all $t\in\mathbb{R}_{\geq 0}$.

```coq
(* theories/exp/seely.v *)

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

### Thm 9.5 comult (`seely_comult`, `bang_proj_tuple`, `bang_proj_tupleE`, `sproj1`, `sproj2`)

The comultiplication coherence square is the one the paper draws explicitly, and it is proved in full. Transporting $\mathsf{dig}$ across the binary Seely iso commutes with the $\mathrel{\&}$-projection tuple, as maps ${!B_1}\otimes{!B_2}\to{!({!B_1}\mathrel{\&}{!B_2})}$: $${!\langle{!\pi_1},{!\pi_2}\rangle}\circ\mathsf{dig}_{B_1\mathrel{\&}B_2}\circ\mathsf{m}^2_{B_1,B_2}\;=\;\mathsf{m}^2_{{!B_1},{!B_2}}\circ(\mathsf{dig}_{B_1}\otimes\mathsf{dig}_{B_2}).$$ The transport datum is `bang_proj_tuple` — the tuple $\langle{!\pi_1},{!\pi_2}\rangle$ built with `icones_tuple` from the $\mathrel{\&}$-projections `sproj1` / `sproj2` — with pairing law `bang_proj_tupleE`. The proof is the chapter's standard recipe: by `tens_excl_charact` it suffices to agree on $x_1^!\otimes x_2^!$, and both sides reduce to $\langle x_1^!,x_2^!\rangle^!$ — the right-hand side through `tensor_morE`, `dig_prom` and `Seely2E` at the unit-ball points $x_1^!,x_2^!$, the left-hand side through `Seely2E` at $x_1,x_2$, then `dig_prom` and `bang_fmap_prom`.

> **Paper — §9** (arXiv 2212.02371, `sec:lin-nonlin-adj`). There is a natural isomorphism $\mathsf{m}^2_{B_1,B_2}$ in $\mathbf{ICones}({!B_1}\otimes{!B_2},{!(B_1\mathrel{\&}B_2)})$ which satisfies $\mathsf{m}^2_{B_1,B_2}(x_1^!\otimes x_2^!)=\langle x_1,x_2\rangle^!$ (this equation fully characterizes $\mathsf{m}^2_{B_1,B_2}$ by Lemma 9.2).

```coq
(* theories/exp/seely.v — Section Seely, Variables (R : realType) (Ar : MeasSubcat R) *)

Definition sproj1.

Definition sproj2.

Definition bang_proj_tuple.

Lemma bang_proj_tupleE.

Lemma seely_comult.
```

### Thm 9.5 coherence (`seely_assoc`, `seely_braid`, `seely_lunit`, `seely_runit`, `seely_der_unit`, `seely_der1`, `seely_der2`)

The coherence witnesses the `SeelyCategory` record lists as fields are named lemmas. `seely_assoc` and `seely_braid` are the strong-monoidal-functor squares of $({!},\mathsf{m}^2)$ against the associators and braidings, $\alpha^\otimes$ vs $\alpha^{\mathrel{\&}}$ and $\sigma^\otimes$ vs $\sigma^{\mathrel{\&}}$; `seely_lunit` and `seely_runit` are the unit squares relating $\mathsf{m}^0$ and $\mathsf{m}^2$ to $\lambda^\otimes/\lambda^{\mathrel{\&}}$ and $\rho^\otimes/\rho^{\mathrel{\&}}$, and use the mixed unit extensionality `tens_excl_unitL` / `tens_excl_unitR` (a map $1\otimes{!B}\to C$ is determined on $1\otimes x^!$). `seely_der_unit` is the counit/unit square $\mathsf{der}_\top\circ\mathsf{m}^0=\;!$, immediate from terminality of $\top$ (`Stop_mor_unique`), and `seely_der1` / `seely_der2` are the binary counit square in projected form. Each of the first four is discharged by the standard recipe — agree on promoted pure tensors via `tens_excl_charact` (or its ternary form `tens_excl_charact3l`), then compute with `Seely2E`, `Seely0E`, `bang_fmap_prom` and `tensor_morE`.

> **Paper — Theorem 9.5** (arXiv 2212.02371). Equipped with the strong monoidal comonad $!$, the category $\mathbf{ICones}$ is a Seely category in the sense of Melliès.

> **Difference.** The counit compatibility with $\mathsf{m}^2$ is recorded in **projected** form: instead of one equation $\mathsf{der}_{B_1\mathrel{\&}B_2}\circ\mathsf{m}^2_{B_1,B_2}:{!B_1}\otimes{!B_2}\to B_1\mathrel{\&}B_2$, there are two, `seely_der1` and `seely_der2`, one per $\mathrel{\&}$-projection. *Why:* $\mathrel{\&}$ and $\otimes$ are genuinely different objects here and there is no canonical comparison $B_1\mathrel{\&}B_2\leftrightarrow B_1\otimes B_2$ through which the un-projected square could be phrased. The projected pair carries the same content — a map into a product is determined by its projections — and each projection is the naturality of $\mathsf{der}$ (`der_nat`) transported across $\mathsf{m}^2$. Nothing here is axiomatised: every coherence law, and the Seely isos themselves, are proved.

```coq
(* theories/exp/seely.v — Section Seely, Variables (R : realType) (Ar : MeasSubcat R) *)

Lemma seely_assoc.

Lemma seely_braid.

Lemma tens_excl_unitL.

Lemma tens_excl_unitR.

Lemma seely_lunit.

Lemma seely_runit.

Lemma seely_der_unit.

Lemma seely_der1.

Lemma seely_der2.
```

```coq
(* theories/exp/seely_defs.v *)

Definition Stop_mor.

Lemma Stop_mor_unique.
```

### Thm 9.7 (`Coalg`, `Coalg_dirac`, `dirac_dense`, `FMeas_coalgebra`, `FMeas_fmap`)

For each $X\in\mathbf{Ar}$, the finite-measure cone $\mathsf{FMeas}(X)$ carries a $!$-coalgebra structure $\mathsf{h}_X\in\mathbf{ICones}(\mathsf{FMeas}(X),{!\mathsf{FMeas}(X)})$, defined via Theorem 6.1 as the integral of the Dirac path composed with the universal nonlinear map, so $\mathsf{h}_X(\mu)=\int_{r\in X}(\boldsymbol\delta^X(r))^!\,\mu(dr)$ and $\mathsf{h}_X(\boldsymbol\delta^X(r))=(\boldsymbol\delta^X(r))^!$. The coalgebra laws follow because the two sides agree on all Dirac measures (`dirac_dense`, paper Theorem 6.2), which are norm-dense. The assignment $X\mapsto\mathsf{FMeas}(X)$ then extends to a functor $\mathbf{Ar}\to\mathbf{ICones}^!$ acting on morphisms by pushforward $\mathsf{FMeas}(\phi)=\phi_\ast$.

> **Paper — Theorem 9.7** (arXiv 2212.02371, `th:meas-cone-coalgebra-stab`). Equipped with $\mathsf{h}_X$, the object $\mathsf{FMeas}(X)$ of $\mathbf{ICones}$ is a coalgebra of the comonad ${!}\_$. Moreover for each $\phi\in\mathbf{Ar}(X,Y)$, we have $\mathsf{FMeas}(\phi)=\phi_\ast\in\mathbf{ICones}^!(\mathsf{FMeas}(X),\mathsf{FMeas}(Y))$ so that $\mathsf{FMeas}$ is a functor $\mathbf{Ar}\to\mathbf{ICones}^!$.

> **Paper — §9** (arXiv 2212.02371, `sec:stable-exp-meas-coalg`). We define $\mathsf{h}_X=\mathcal{I}^{{!\mathsf{FMeas}(X)}}_X(\mathsf{nl}_{\mathsf{FMeas}(X)}\circ\boldsymbol\delta^X)\in\mathbf{ICones}(\mathsf{FMeas}(X),{!\mathsf{FMeas}(X)})$ using Theorem 6.1. In other words $\mathsf{h}_X(\mu)=\int_{r\in X}(\boldsymbol\delta^X(r))^!\,\mu(dr)$ and it satisfies $\mathsf{h}_X(\boldsymbol\delta^X(r))=(\boldsymbol\delta^X(r))^!$.

```coq
(* theories/exp/coalgebra.v *)

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

### Thm 9.7 functor (`is_coalg_mor`, `coalg_mor_id`, `coalg_mor_comp`, `FMeas_fmap_dirac`, `FMeas_fmap_is_coalg_mor`)

The functoriality half of Thm 9.7 — "$\mathsf{FMeas}$ is a functor $\mathbf{Ar}\to\mathbf{ICones}^!$" — has three named witnesses. `is_coalg_mor` is the property that makes an `icones_hom` a morphism of $!$-coalgebras, $b\circ h={!h}\circ a$; `coalg_mor_id` and `coalg_mor_comp` show that identities have it and that it is stable under composition, so the coalgebras and these morphisms do form a category. `FMeas_fmap_is_coalg_mor` is the theorem itself: the pushforward $\mathsf{FMeas}(\phi)=\phi_\ast$ is a coalgebra morphism $(\mathsf{FMeas}(X),\mathsf{h}_X)\to(\mathsf{FMeas}(Y),\mathsf{h}_Y)$. Its proof is Thm 6.2 again — by `dirac_dense` it is enough to check both sides on a Dirac, where the left-hand side is $\mathsf{h}_Y(\boldsymbol\delta^{Y}(\phi\,r))=(\boldsymbol\delta^{Y}(\phi\,r))^!$ using the computation law `FMeas_fmap_dirac`, and the right-hand side is ${!\mathsf{FMeas}(\phi)}((\boldsymbol\delta^{X}(r))^!)$, which is the same by `bang_fmap_prom` (Lem 9.3).

> **Paper — Theorem 9.7** (arXiv 2212.02371, `th:meas-cone-coalgebra-stab`). Moreover for each $\phi\in\mathbf{Ar}(X,Y)$, we have $\mathsf{FMeas}(\phi)=\phi_\ast\in\mathbf{ICones}^!(\mathsf{FMeas}(X),\mathsf{FMeas}(Y))$ so that $\mathsf{FMeas}$ is a functor $\mathbf{Ar}\to\mathbf{ICones}^!$.

> **Difference.** The paper reads the conclusion inside the category $\mathbf{ICones}^!$; `coalgebra.v` records it as a *property* of an `icones_hom` (`is_coalg_mor`) together with the identity and composition closure lemmas, and does not bundle the Eilenberg–Moore category here. *Why:* the § 9 file only needs the property (Thm 9.7 and the $\mathsf{FMeas}$ action), and bundling would drag in the whole EM layer; the bundled category — `coalg_hom`, `coalg_id`, `coalg_comp`, `EM_Cat` / `ICones_EM` — is built downstream in `theories/cbv/em_cat.v` and documented under *Beyond the paper*.

```coq
(* theories/exp/coalgebra.v — Section Coalgebra, Variables (R : realType) (Ar : MeasSubcat R) *)

Definition is_coalg_mor.

Lemma coalg_mor_id.

Lemma coalg_mor_comp.

Lemma FMeas_fmap_dirac.

Lemma FMeas_fmap_is_coalg_mor.
```

---

## Beyond the paper — paper-cited meta-theorems we mechanised in full

The paper *cites* a number of categorical / linear-logic results as black
boxes (SAFT, Fox's theorem, Lack's lifting, Melliès §7.4 Prop 28 / Prop 20 /
Prop 29) which a textbook reader can take on trust. A machine-checked
development cannot cite a black box; the following constructions are real
mathematical content the formalisation adds *to discharge the paper's
citations*. Each is grounded against its **external** reference — Riehl's
*Category Theory in Context*, Fox's *Coalgebras and cartesian categories*,
and Melliès' *Categorical Semantics of Linear Logic* — rather than against
arXiv 2212.02371.

The PPL-side beyond-the-paper content (Boolean cascade, CBV value-fixpoint,
the surface language and its examples) is in the [PPL tab](../ppl/).

| Item | English statement | Rocq |
|---|---|---|
| SAFT engine | Freyd's special adjoint functor theorem, mechanised concretely: a complete, well-powered, locally small category with a small coseparator has a left adjoint to every continuous functor, built as a wide intersection of subobjects of a power of the coseparator. | `SubobjClassifier`, `wi_obj`, `wi_med`, `is_icones_left_adjoint` — `theories/homs/representable.v` |
| Tensor as SAFT left adjoint | $-\otimes C$ is constructed as the SAFT left adjoint of $(C\multimap -)$, using the concrete SAFT engine, so the tree carries no `Parameter`/`Axiom`. | `tensor`, `tensor_incl` — `theories/homs/tensor_construct.v` |
| Exponential as SAFT left adjoint | $\;! = E$ is constructed as the SAFT left adjoint of $\mathsf{Der}$, instantiating the shared SAFT engine (`saft_construct.v`) behind a `Qed`-sealed pack. | `bang_sig`, `bang_pack`, `Bang`, `nl`, `lin` — `theories/exp/bang_construct.v` |
| EM category | The Eilenberg–Moore category $\mathrm{EM}(!)$ of the exponential comonad, as a category: bundled coalgebra morphisms, identity, composition and the three category laws, packaged as a record with a canonical witness. | `coalg_hom`, `coalg_id`, `coalg_comp`, `EM_Cat`, `ICones_EM` — `theories/cbv/em_cat.v` |
| Cofree adjunction | The forgetful $U$ is left adjoint to the cofree functor $\tilde{!}B=({!B},\mathrm{dig}_B)$, presented by an explicit hom-set bijection with both round-trips, naturality in both arguments, unit / counit and the two triangle identities. | `bang_cofree`, `U_obj`, `adj_phi`, `adj_psi`, `adj_triangleL`, `adj_triangleR` — `theories/cbv/em_cat.v` |
| Melliès LC2 comonoid | Every cofree object $!A$ carries a *commutative comonoid* $({!A},d_A,e_A)$, built by transporting the cartesian diagonal / terminal of $(\mathbin{\&},\top)$ across the Seely isomorphisms; the four comonoid laws are proved, not assumed. | `d_bang`, `e_bang`, `comonoid_coassoc`, `comonoid_counitL`, `comonoid_counitR`, `comonoid_cocomm` — `theories/cbv/em_seely_comonoid.v` |
| Melliès LC3 / LC4 | $d_A$ and $e_A$ are $!$-coalgebra morphisms into the *transported* coalgebras $!A\otimes{!A}$ and $1$ (the LC1-level symmetric-monoidal structure of $\mathrm{EM}(!)$), and $\mathrm{dig}_A$ is a morphism of comonoids. | `tens_cofree`, `unit_cofree`, `d_bang_is_coalg_mor`, `e_bang_is_coalg_mor`, `dig_comonoid_mult`, `dig_comonoid_counit` — `theories/cbv/em_seely_comonoid.v` |
| Lax comparison m | The lax symmetric-monoidal comparison $m_{A,B} : {!A}\otimes{!B}\multimap{!(A\otimes B)}$, its promoted-point law $m(x^!\otimes y^!)=(x\otimes y)^!$ and its coalgebra-morphism property — the structure map that makes the $\mathrm{EM}(!)$ product $A\otimes B$ a coalgebra. | `m_bang`, `m_bang_prom`, `m_bang_is_coalg_mor`, `EM_prod`, `EM_prod_str`, `EM_term` — `theories/cbv/em_cartesian.v` |
| Melliès Prop 26 | Every $!$-coalgebra $(A,h_A)$ is a retract of its cofree coalgebra $(!A,\delta_A)$ in $\mathrm{EM}(!)$. | `diagram81` — `theories/cbv/em_cartesian.v` |
| Melliès Prop 20 | Retraction lifting: if $i$ is a coalgebra morphism with carrier retraction $r\circ i = \mathrm{id}$ and $i\circ f$ is a coalgebra morphism, then $f$ is a coalgebra morphism. | `coalg_mor_lift` — `theories/cbv/em_cartesian.v` |
| Melliès Prop 27 | A retract of a commutative comonoid lifts to a commutative comonoid; the four transported comonoid laws. | `transp_counitL`, `transp_counitR`, `transp_cocomm`, `transp_coassoc` — `theories/cbv/em_cartesian.v` |
| Melliès Prop 28 | The monoidal structure of a linear category is cartesian in $\mathrm{EM}(!)$; the comonoid predicate holds on **every** coalgebra. | `EMComon_all` — `theories/cbv/em_cartesian.v` |
| Comonoidality corollaries | The two distinguished families are comonoidal as immediate specialisations of the unconditional `EMComon_all`: the cofree coalgebras $\tilde{!}B$, and the paper-Thm-9.7 coalgebras $\mathsf{FMeas}(X)$ — the latter is what makes every measurable base context duplicable in the CBV interpreter. | `EMComon_cofree`, `EMComon_FMeas` — `theories/cbv/em_cartesian.v` |
| Melliès Cor 17 | A symmetric monoidal category in which every object carries a monoidal-natural comonoid is cartesian, with product the tensor and terminal object the unit. | `ICones_EM_cartesian`, `EM_Cartesian` — `theories/cbv/em_cartesian.v` |
| EM product laws | The cartesian universal property of the $\otimes$-product in $\mathrm{EM}(!)$, spelled out: the pairing $\langle f,g\rangle=(f\otimes g)\circ d_Z$, the two $\beta$-laws $\pi_i\circ\langle f,g\rangle$, and the terminal uniqueness $h=\mathrm{coalg\_e}\,P$ — the witnesses the `EM_Cartesian` record elides as comments. | `em_pair_mor`, `em_proj1_pair`, `em_proj2_pair`, `em_term_unique` — `theories/cbv/em_cartesian.v` |
| Fox η-law cofree | The cartesian η-law $\langle\pi_1,\pi_2\rangle = \mathrm{id}$ on cofree coalgebra pairs. | `em_pair_mor_proj_id_cofree` — `theories/cbv/cbv_adjunction.v` |
| Fox η-law general | The cartesian η-law $\langle\pi_1,\pi_2\rangle = \mathrm{id}$ for the $\mathrm{EM}(!)$ binary product on **every** pair of coalgebras. | `em_pair_mor_proj_id` — `theories/cbv/cbv_adjunction.v` |
| Melliès Prop 29 | The cofree-coalgebra adjunction $U\dashv\tilde{!} : \mathbf{ICones}\rightleftarrows\mathrm{EM}(!)$ is a linear/non-linear (lax symmetric monoidal) adjunction. | `CBV_Model`, `ICones_CBV` — `theories/cbv/cbv_adjunction.v` |
| Lax coherence of m | The lax symmetric-monoidal coherence of $\tilde{!}$ at the $m$-level — associativity, both unitors and the symmetry against $\alpha/\lambda/\rho/\sigma$ — plus the packaged LNL monoidality witnesses ($m_2$, $m_0$ and the monoidal counit / unit laws) that `CBV_Model` carries as elided fields. | `m_bang_assoc`, `m_bang_lunit`, `m_bang_runit`, `m_bang_braid`, `bang_m`, `bang_e0`, `adj_counit_monoidal2` — `theories/cbv/cbv_adjunction.v` |
| FMeas lax monoidal | The monoidal comparison of the paper's own $\mathsf{FMeas}$ functor: $\mathsf{FMeas}(X)\otimes\mathsf{FMeas}(Y)\multimap\mathsf{FMeas}(X\times Y)$ sending a pure tensor to the product measure and $\delta_x\otimes\delta_y$ to $\delta_{(x,y)}$. Its construction discharges the previously-deferred paper-§6 follow-up to Thm 6.1, path preservation *in the cone variable*. | `fmeas_lax`, `fmeas_lax_E`, `fmeas_lax_dirac` — `theories/cbv/fmeas_lax.v`; `int_to_linhom_pres_path_in_cone` — `theories/homs/bilin.v` |

### SAFT engine (`SubobjClassifier`, `wi_obj`, `wi_med`, `is_icones_left_adjoint`)

The paper builds $\otimes$, $!$, and the Seely isos via Freyd's Special Adjoint Functor Theorem (SAFT), invoked as a black box. Rather than postulate it, we mechanise the SAFT argument concretely: the left adjoint of a continuous functor $F$ at $c$ is the *wide intersection* of the subobjects of a power of the coseparator $1$ over which $c\to F-$ factors. The engine is a subobject classifier (well-poweredness), binary and wide intersections of subobjects with their universal properties, an initiality argument, and the hom-bijection export contract a left-adjoint candidate must satisfy.

> **Source — Riehl, *Category Theory in Context*, Theorem 4.6.10 (Special Adjoint Functor Theorem)** (Dover/Cambridge, 2016; Theorem 4.7.10 in the online edition). Let $U : A \to S$ be a continuous functor whose domain is complete and whose domain and codomain are locally small. Furthermore, if $A$ has a small coseparating set and every collection of subobjects of a fixed object in $A$ admits an intersection, then $U$ admits a left adjoint.

> **Source — Riehl, *ibid.*, Lemma 4.6.11** (Lemma 4.7.11 online). Suppose $C$ is locally small, complete, has a small coseparating set $\Phi$, and has the property that every collection of subobjects has an intersection. Then $C$ has an initial object. (Proof: form the product $p = \prod_{k\in\Phi} k$ and the intersection $i \hookrightarrow p$ of all subobjects of $p$; then $i$ is initial.)

> **Source — Riehl, *ibid.*, Corollary 4.6.14** (Corollary 4.7.14 online). Suppose $C$ is locally small, complete, has a small coseparating set, and has the property that every collection of subobjects of a fixed object has an intersection. Then any continuous functor $F : C \to \mathbf{Set}$ is representable.

> **Difference.** SAFT is a *meta-theorem* about the existence of an adjoint; the mechanisation replaces the abstract statement with the concrete construction its proof supplies. `SubobjClassifier` / `icones_well_powered` discharge well-poweredness (Riehl's "each object admits only a set's worth of subobjects"); `pb_med` and `wi_obj`/`wi_med` build the binary and wide intersections of Lemma 4.6.11; and `is_icones_left_adjoint` records the hom-bijection contract a candidate left adjoint must satisfy. The coseparator is the unit cone $1$ (paper Thm 4.18), not the interval $I$ of Riehl's Stone–Čech example.

```coq
(* theories/homs/representable.v *)
Record SubobjClassifier : Type := MkClassifier {
  cls_S : set B; cls_add : B -> B -> B; cls_scl : {nonneg R} -> B -> B;
  cls_zer : B; cls_nrm : B -> R;
  cls_M : forall X : ar_obj Ar, set (ar_carrier Ar X -> B -> R);
}.

Theorem icones_well_powered :
  exists cls : icones_subobject B -> SubobjClassifier B,
    forall D1 D2 : icones_subobject B,
      cls D1 = cls D2 -> subobject_equiv D1 D2.

Definition wi_obj  : ICone.type Ar := icones_eq wi_u wi_v.
Definition wi_med : icones_hom Ar Z wi_obj :=
  icones_eq_med wi_u wi_v wi_tuple wi_tuple_equ.
Lemma wi_med_proj (k : K) : icones_comp (wi_proj k) wi_med = ff k.
Lemma wi_med_unique (kk : icones_hom Ar Z wi_obj) :
  (forall k, icones_comp (wi_proj k) kk = ff k) -> kk = wi_med.

Definition is_icones_left_adjoint
    (Cobj : Type) (Homc : Cobj -> Cobj -> Type)
    (Robj : ICone.type Ar -> Cobj) (Fobj : Cobj -> ICone.type Ar)
    (Phi : forall (c : Cobj) (x : ICone.type Ar),
             icones_hom Ar (Fobj c) x -> Homc c (Robj x))
    (Psi : forall (c : Cobj) (x : ICone.type Ar),
             Homc c (Robj x) -> icones_hom Ar (Fobj c) x) : Prop :=
  (forall c x (f : icones_hom Ar (Fobj c) x), Psi c x (Phi c x f) = f) /\
  (forall c x (g : Homc c (Robj x)), Phi c x (Psi c x g) = g).
```

### Tensor as SAFT left adjoint (`tensor`, `tensor_incl`)

The tensor $-\otimes C$ is discharged as the SAFT left adjoint of the internal-hom functor $(C\multimap -)$: the tensor object $B\otimes C$ is the wide intersection of the family of factoring subobjects of the product $\prod (C\multimap -)$, indexed by the well-powered classifier, with curry/uncurry and naturality built on top.

> **Source — Riehl, *Category Theory in Context*, Theorem 4.6.10** (as above). A continuous functor out of a complete, locally small, well-powered category with a small coseparator admits a left adjoint; concretely the left adjoint at $c$ is the wide intersection of the subobjects of a power of the coseparator through which $c\to F-$ factors.

> **Difference.** The paper (Thm 5.9) shows $C\multimap -$ preserves all limits and then *invokes* SAFT to produce the tensor; the mechanisation runs the concrete intersection construction of the previous entry, so `tensor` and `tensor_incl` are honest definitions rather than a `Parameter` interface. The limit-preservation hypothesis is discharged in `theories/homs/limpl_continuous.v`; the measurability crux of the currying iso lives in `tensor_hom_iso.v` / `tensor_iso.v`.

```coq
(* theories/homs/tensor_construct.v *)
Module Icones_tensor_construct.
(* family of factoring subobjects of the product p = (C ⊸ −),
   indexed by the well-powered classifier *)
Definition tensor : ICone.type Ar := wi_obj fhh fk0.
Definition tensor_incl : icones_hom Ar tensor p := wi_incl fAdom fhh fk0.
(* + curry / uncurry / naturality, the SAFT discharge *)
End Icones_tensor_construct.
```

### Exponential as SAFT left adjoint (`bang_sig`, `bang_pack`, `Bang`, `nl`, `lin`)

The exponential $! = E$ is discharged as the SAFT left adjoint of the dereliction functor $\mathsf{Der}$, by instantiating the shared parametric SAFT engine of `theories/homs/saft_construct.v` at the signature `bang_sig` (hom-sets $\mathbf{SCones}(B, X)$, action $\mathsf{Der}\,h \circ -$; products preserved on the nose by `scones_tuple`, equalisers by `der_eq_med`): the object $\mathrm{Bang}\,B = E\,B$ is the engine's wide intersection of the factoring subobjects of the coseparator power $1^{\mathbf{SCones}(B,\mathbb{1})}$, with the universal nonlinear map `nl` (the engine's universal element) and the linear factoriser `lin` (the engine's mediator). Unlike the tensor instance, the instantiation is **sealed**: the engine output is packed in the Σ-type witness `bang_pack`, closed with `Qed`, and `Bang` / `nl` / `lin` are thin projections of that kernel-opaque pack — so their normal forms are atomic and the nested-`Bang` comonad proofs of `bang.v` never unfold the SAFT construction.

> **Source — Riehl, *Category Theory in Context*, Theorem 4.6.10** (as above). A continuous functor out of a complete, locally small, well-powered category with a small coseparator admits a left adjoint, given concretely by the wide intersection of the factoring subobjects of a power of the coseparator.

> **Difference.** The paper's §7 (Thm 7.34) supplies the limit-preservation of $\mathsf{Der}$ and then invokes SAFT for $!$; the mechanisation runs the shared concrete engine behind the `Qed`-sealed pack, so `Bang`, `nl`, `lin` are proved definitions with no axiom interface (`Print Assumptions` traverses the sealed pack; only the three `boolp` classical axioms remain). Continuity of $\mathsf{Der}$ (Thm 7.34) is in `theories/stable/der_continuous.v`.

```coq
(* theories/exp/bang_construct.v *)
Definition bang_sig : SC.saft_sig Ar :=
  @SC.MkSaftSig R Ar bang_ehom bang_emap bang_emap_id bang_emap_comp
    bang_emap_mono bang_etuple bang_etuple_proj bang_eprod_ext
    bang_eq_med bang_eq_med_factor.

Definition Bang : ICone.type Ar := projT1 bang_pack.

Definition nl : scones_hom B Bang := projT1 (projT2 bang_pack).

Definition lin (C : ICone.type Ar) (f : scones_hom B C) :
    icones_hom Ar Bang C :=
  proj1_sig (projT2 (projT2 bang_pack)) C f.
```

### EM category (`coalg_hom`, `coalg_id`, `coalg_comp`, `EM_Cat`, `ICones_EM`)

The comonad $(!,\mathrm{der},\mathrm{dig})$ has an Eilenberg–Moore category $\mathrm{EM}(!)$: objects are the $!$-coalgebras $(A,a)$ of `Coalgebra` (paper Thm 9.7), morphisms are `icones_hom`s that commute with the structure maps. The formalisation *bundles* the side condition into a single morphism type `coalg_hom` (so $\mathrm{EM}(!)$ has one hom-type, matching the project's concrete-category style), proves that two bundled morphisms are equal as soon as their carriers agree (`coalg_hom_eqP`, the side condition being a `Prop`), and derives the three category laws `coalg_compIl` / `coalg_compIr` / `coalg_compA` from the `ICones` ones. The package is the record `EM_Cat` with canonical witness `ICones_EM`.

> **Source — Mac Lane, *Categories for the Working Mathematician*, 2nd ed. (GTM 5, Springer 1998), §VI.2 "Algebras for a monad", Theorem 1.** *(Faithful paraphrase, dualised to comonads.)* For a monad $\langle T,\eta,\mu\rangle$ in a category $X$, the $T$-algebras and their morphisms form a category $X^{T}$, and the forgetful functor $G^{T}:X^{T}\to X$ has a left adjoint $F^{T}$ with $G^{T}F^{T}=T$. Dually, for a comonad $\langle !,\varepsilon,\delta\rangle$ the $!$-coalgebras and coalgebra morphisms form the Eilenberg–Moore category $\mathrm{EM}(!)$, whose identities and composites are those of the underlying category.

> **Difference.** Mac Lane's $X^{T}$ has *unbundled* morphisms (a carrier map plus a commuting square stated separately). The mechanisation bundles them as `coalg_hom` so that the category laws are literal Leibniz equalities of a single type; the price is `coalg_hom_eqP`, which recovers "equal iff the carriers are equal" from proof irrelevance on the `Prop`-valued side condition. `EM_Cat` is a record-with-witness in the style of `Comonad` / `SeelyCategory` — the project carries no abstract `Category` class.

```coq
(* theories/cbv/em_cat.v *)
Record coalg_hom (P Q : Coalgebra Ar) : Type := MkCoalgHom { ch_mor : _; ch_is_mor : _ }.
Lemma coalg_hom_eqP (P Q : Coalgebra Ar) (f g : coalg_hom P Q) : ch_mor f = ch_mor g -> f = g.
Definition coalg_id (P : Coalgebra Ar) : coalg_hom P P.
Definition coalg_comp (P Q S : Coalgebra Ar) (g : coalg_hom Q S) (f : coalg_hom P Q) : coalg_hom P S.
Lemma coalg_compIl (P Q : Coalgebra Ar) (f : coalg_hom P Q) : coalg_comp (coalg_id Q) f = f.
Lemma coalg_compIr (P Q : Coalgebra Ar) (f : coalg_hom P Q) : coalg_comp f (coalg_id P) = f.
Lemma coalg_compA (P Q S T : Coalgebra Ar) (h : coalg_hom S T) (g : coalg_hom Q S) (f : coalg_hom P Q) :
  coalg_comp h (coalg_comp g f) = coalg_comp (coalg_comp h g) f.
Record EM_Cat (R : realType) (Ar : MeasSubcat R) : Type := MkEMCat { em_obj : _; em_hom : _ }.
Definition ICones_EM (R : realType) (Ar : MeasSubcat R) : EM_Cat Ar.
```

### Cofree adjunction (`bang_cofree`, `U_obj`, `adj_phi`, `adj_psi`, `adj_triangleL`, `adj_triangleR`)

The cofree coalgebra on $B$ is $\tilde{!}B=({!B},\mathrm{dig}_B)$ — a coalgebra by the comonad's counit and coassociativity laws — with functorial action $\tilde{!}f={!f}$ (a coalgebra morphism by naturality of $\mathrm{dig}$) and functoriality `bang_cofree_fmap_id` / `bang_cofree_fmap_comp`. The forgetful functor $U$ takes $(A,a)$ to its carrier. The adjunction $U\dashv\tilde{!}$ is presented by the hom-set bijection
$$\mathrm{EM}(!)\bigl(\gamma,\tilde{!}B\bigr)\;\cong\;\mathbf{ICones}\bigl(U\gamma,B\bigr),$$
$\Phi\,h=\mathrm{der}_B\circ U h$ and $\Psi\,g={!g}\circ a$, mutually inverse (`adj_phiK` / `adj_psiK`) and natural in *both* arguments (`adj_phi_natL` contravariantly in the coalgebra, `adj_phi_natR` covariantly in the object). The unit is the coalgebra structure map (`adj_unit`, a coalgebra morphism exactly by `coalg_coassoc`) and the counit is dereliction (`adj_counit`); the two triangles `adj_triangleL` / `adj_triangleR` are exactly `coalg_counit` and `comonad_counitR`. `adj_psi` is the workhorse the CBV interpreter uses to promote a linear map at a setlike environment (see the [PPL tab](../ppl/)).

> **Source — Mac Lane, *ibid.*, §VI.2, Theorem 1 / §VI.3.** *(Faithful paraphrase, dualised to comonads.)* The forgetful functor from the Eilenberg–Moore category of a monad has a left adjoint, the free-algebra functor, and the monad is recovered as the composite; the unit and counit of that adjunction are the monad unit and the algebra structure maps. Dually, for a comonad $!$ on $L$ the forgetful $U:\mathrm{EM}(!)\to L$ is *left* adjoint to the cofree functor $\tilde{!}B=({!B},\delta_B)$, with counit $\varepsilon$ and unit the coalgebra structure maps, and ${!}=U\circ\tilde{!}$.

> **Difference.** The textbook statement asserts *existence* of the adjoint; the mechanisation exhibits $\Phi$ and $\Psi$ as definitions and proves the four equations (`adj_phiK`, `adj_psiK`, `adj_triangleL`, `adj_triangleR`) plus naturality in both arguments as separate lemmas, because downstream code (the CBV interpreter) *computes* with $\Psi$ rather than merely invoking the bijection. Both triangle identities reduce to laws already in the tree — `coalg_counit` for the $U$-side and `comonad_counitR` for the $\tilde{!}$-side — so nothing new is assumed here.

```coq
(* theories/cbv/em_cat.v *)
Definition bang_cofree (B : ICone.type Ar) : Coalgebra Ar.
Lemma bang_cofree_str (B : ICone.type Ar) : coalg_str (bang_cofree B) = dig B.
Definition bang_cofree_hom (B C : ICone.type Ar) (f : icones_hom Ar B C) : coalg_hom (bang_cofree B) (bang_cofree C).
Lemma bang_cofree_fmap_id (B : ICone.type Ar) : bang_cofree_hom (icones_id Ar B) = coalg_id (bang_cofree B).
Lemma bang_cofree_fmap_comp (B C D : ICone.type Ar) (g : icones_hom Ar C D) (f : icones_hom Ar B C) :
  bang_cofree_hom (icones_comp g f) = coalg_comp (bang_cofree_hom g) (bang_cofree_hom f).
Definition U_obj (P : Coalgebra Ar) : ICone.type Ar.
Definition U_mor (P Q : Coalgebra Ar) (h : coalg_hom P Q) : icones_hom Ar (U_obj P) (U_obj Q).
Definition adj_counit (B : ICone.type Ar) : icones_hom Ar (U_obj (bang_cofree B)) B.
Definition adj_unit (P : Coalgebra Ar) : coalg_hom P (bang_cofree (U_obj P)).
Definition adj_phi (P : Coalgebra Ar) (B : ICone.type Ar) (h : coalg_hom P (bang_cofree B)) : icones_hom Ar (U_obj P) B.
Definition adj_psi (P : Coalgebra Ar) (B : ICone.type Ar) (g : icones_hom Ar (U_obj P) B) : coalg_hom P (bang_cofree B).
Lemma adj_phiK (P : Coalgebra Ar) (B : ICone.type Ar) (g : icones_hom Ar (U_obj P) B) : adj_phi (adj_psi g) = g.
Lemma adj_psiK (P : Coalgebra Ar) (B : ICone.type Ar) (h : coalg_hom P (bang_cofree B)) : adj_psi (adj_phi h) = h.
Lemma adj_phi_natL (P P' : Coalgebra Ar) (B : ICone.type Ar) (h : coalg_hom P (bang_cofree B)) (k : coalg_hom P' P) :
  adj_phi (coalg_comp h k) = icones_comp (adj_phi h) (U_mor k).
Lemma adj_phi_natR (P : Coalgebra Ar) (B B' : ICone.type Ar) (h : coalg_hom P (bang_cofree B)) (f : icones_hom Ar B B') :
  adj_phi (coalg_comp (bang_cofree_hom f) h) = icones_comp f (adj_phi h).
Lemma adj_triangleL (P : Coalgebra Ar) : adj_phi (adj_unit P) = icones_id Ar (U_obj P).
Lemma adj_triangleR (B : ICone.type Ar) : adj_psi (adj_counit B) = coalg_id (bang_cofree B).
```

### Melliès LC2 comonoid (`d_bang`, `e_bang`, `diag`, `term`, `d_bang_prom`, `e_bang_prom`, `comonoid_coassoc`, `comonoid_counitL`, `comonoid_counitR`, `comonoid_cocomm`)

Every cofree object $!A$ carries the commutative-comonoid structure a Melliès *linear category* requires. The comultiplication is $d_A=\mathrm{Seely2}^{-1}_{A,A}\circ{!(\Delta_A)}$ for the cartesian diagonal $\Delta_A=\langle\mathrm{id},\mathrm{id}\rangle$ of $(\mathbin{\&},\top)$ (`diag`), and the counit is $e_A=\mathrm{Seely0}^{-1}\circ{!(\langle\rangle_A)}$ for the terminal map (`term`, the `Stop_mor` of `scones_ccc.v`). On a promoted point of the unit ball they compute as $d_A(x^!)=x^!\otimes x^!$ and $e_A(x^!)=1$, and the four comonoid laws — coassociativity, both counit laws and cocommutativity — follow by `bang_ext` extensionality plus the structural-iso computation laws of the tensor.

> **Source — Melliès, *Categorical Semantics of Linear Logic* (Panoramas et Synthèses 27, SMF 2009), §7.4 "Linear categories", condition LC2.** *(Faithful paraphrase, after Bierman's definition.)* A *linear category* is a symmetric monoidal closed category $L$ together with a symmetric monoidal comonad $(!,\varepsilon,\delta)$ such that **(LC1)** the comonad is symmetric monoidal, so that its Eilenberg–Moore category inherits a symmetric monoidal structure; **(LC2)** every object $!A$ carries a *commutative comonoid* $({!A},d_A,e_A)$, i.e. $d_A$ is coassociative and cocommutative and $e_A$ is a two-sided counit for it; **(LC3)** $d_A$ and $e_A$ are $!$-coalgebra morphisms; and **(LC4)** $\delta_A$ is a morphism of comonoids.

> **Difference.** Melliès (and Bierman) take $(d,e)$ as *given data* of a linear category, subject to LC2–LC4 as axioms. Here they are *constructed*: $d_A$ and $e_A$ are transported from the cartesian $(\Delta_A,\langle\rangle_A)$ of the $\mathbf{SCones}$ product $(\mathbin{\&},\top)$ across the Seely isomorphisms of paper Thm 9.5, so LC2 becomes a *theorem* about $\mathbf{ICones}$ rather than a hypothesis. Its proof is the chapter's standing recipe — apply `bang_ext`, compute both sides on a promoted point $x^!$ where $\mathrm{der}$, $\mathrm{dig}$ and $!f$ all have transparent values, then finish with `Seely2E` / `Seely0E` and the pure-tensor laws `tensor_lunitEp` / `tensor_runitEp` / `tensor_assocEp` / `tensor_braidEp`. Note that $\Delta_A$ lives in $\mathbf{SCones}$, not $\mathbf{ICones}$: the diagonal of a *linear* category is not linear, which is exactly why it must be routed through $!$.

```coq
(* theories/cbv/em_seely_comonoid.v *)
Definition diag (A : ICone.type Ar) : icones_hom Ar A (sprod A A).
Definition term (A : ICone.type Ar) : icones_hom Ar A (Stop Ar).
Definition d_bang (A : ICone.type Ar) : icones_hom Ar (Bg A) (Bg A ⊗ Bg A).
Lemma d_bang_prom (A : ICone.type Ar) (x : A) : cone_norm x <= 1 -> Lfun (d_bang A) x! = x! ⊗p x!.
Definition e_bang (A : ICone.type Ar) : icones_hom Ar (Bg A) (cone_one_car Ar).
Lemma e_bang_prom (A : ICone.type Ar) (x : A) : cone_norm x <= 1 -> Lfun (e_bang A) x! = one1.
Lemma comonoid_coassoc (A : ICone.type Ar) : _.
Lemma comonoid_counitL (A : ICone.type Ar) : _.
Lemma comonoid_counitR (A : ICone.type Ar) : _.
Lemma comonoid_cocomm (A : ICone.type Ar) :
  icones_comp (iso_fwd (tensor_braid (Bg A) (Bg A))) (d_bang A) = d_bang A.
```

### Melliès LC3 / LC4 (`tens_cofree`, `unit_cofree`, `d_bang_is_coalg_mor`, `e_bang_is_coalg_mor`, `dig_comonoid_mult`, `dig_comonoid_counit`)

For LC3 the *targets* have to be coalgebras, and they are obtained by transport, not by an abstract lifting theorem: $!A\otimes{!B}$ inherits the cofree structure of $!(A\mathbin{\&}B)$ across $\mathrm{Seely2}$ (`tens_cofree_str`, packaged as the coalgebra `tens_cofree`), and $1$ inherits that of $!\top$ across $\mathrm{Seely0}$ (`unit_cofree_str`, packaged as `unit_cofree`). The single computation `tens_cofree_str_prom` — the transported structure sends a promoted pure tensor $x^!\otimes y^!$ to its own promotion $(x^!\otimes y^!)^!$ — is the workhorse of the whole layer: it discharges the transported coassociativity, LC3 for $d$, and (in `em_cartesian.v`) `m_bang_prom`. LC3 then reads $d_A:\tilde{!}A\to{\tt tens\_cofree}\,A\,A$ and $e_A:\tilde{!}A\to{\tt unit\_cofree}$, and LC4 says $\mathrm{dig}_A$ is a comonoid morphism, compatible with $d$ and with $e$.

> **Source — Melliès, *ibid.*, §7.4, conditions LC1, LC3 and LC4.** *(Faithful paraphrase, as above.)* **(LC1)** the symmetric monoidal comonad structure of $!$ lifts the tensor of $L$ to its Eilenberg–Moore category; **(LC3)** for every object $A$ the comultiplication $d_A:{!A}\to{!A}\otimes{!A}$ and the counit $e_A:{!A}\to 1$ are morphisms of $!$-coalgebras, the codomains carrying the lifted (LC1) structures; **(LC4)** the comonad comultiplication $\delta_A:{!A}\to{!!A}$ is a morphism of commutative comonoids, i.e. it commutes with the comultiplications and with the counits.

> **Difference.** Melliès obtains the LC1 lifting of $\otimes$ to $\mathrm{EM}(!)$ from the symmetric monoidal structure of the comonad (Lack's lifting). The mechanisation builds it concretely and *only where it is needed*: `tens_cofree_str` is literally $!(\mathrm{Seely2}^{-1})\circ\mathrm{dig}_{A\mathbin{\&}B}\circ\mathrm{Seely2}$, and `unit_cofree_str` its nullary analogue. This is deliberately still the **symmetric-monoidal** level: `tens_cofree` / `unit_cofree` are *not yet* the cartesian product and terminal object of $\mathrm{EM}(!)$ — that is the content of Melliès Prop 28 / Cor 17 below, and it needs the transported comonoid on *every* coalgebra, not just on cofree ones. The coassociativity law of the transported structure is the one place a *pure-tensor* extensionality is needed (`tens_excl_charact`) rather than the promoted-point `bang_ext`; the unit side uses `one_ext` instead, a morphism out of $1$ being determined by its value at `one1`.

```coq
(* theories/cbv/em_seely_comonoid.v *)
Definition tens_cofree_str (A B : ICone.type Ar) : icones_hom Ar (Bg A ⊗ Bg B) (Bg (Bg A ⊗ Bg B)).
Lemma tens_cofree_str_prom (A B : ICone.type Ar) (x : A) (y : B) :
  cone_norm x <= 1 -> cone_norm y <= 1 -> Lfun (tens_cofree_str A B) (x! ⊗p y!) = (x! ⊗p y!)!.
Definition tens_cofree (A B : ICone.type Ar) : Coalgebra Ar.
Definition unit_cofree_str : icones_hom Ar (cone_one_car Ar) (Bg (cone_one_car Ar)).
Lemma unit_cofree_str_one1 : Lfun unit_cofree_str one1 = one1!.
Definition unit_cofree : Coalgebra Ar.
Lemma one_ext (C : ICone.type Ar) (f g : icones_hom Ar (cone_one_car Ar) C) : Lfun f one1 = Lfun g one1 -> f = g.
Lemma d_bang_is_coalg_mor (A : ICone.type Ar) : is_coalg_mor (bang_cofree A) (tens_cofree A A) (d_bang A).
Lemma e_bang_is_coalg_mor (A : ICone.type Ar) : is_coalg_mor (bang_cofree A) unit_cofree (e_bang A).
Lemma dig_comonoid_mult (A : ICone.type Ar) :
  icones_comp (d_bang (Bg A)) (dig A) = icones_comp (tensor_mor (dig A) (dig A)) (d_bang A).
Lemma dig_comonoid_counit (A : ICone.type Ar) : icones_comp (e_bang (Bg A)) (dig A) = e_bang A.
```

### Lax comparison m (`m_bang`, `m_bang_prom`, `m_bang_is_coalg_mor`, `EM_prod`, `EM_prod_str`, `EM_term`)

The lax symmetric-monoidal structure map of $!$ is $m_{A,B}:{!A}\otimes{!B}\multimap{!(A\otimes B)}$, defined as ${!(\varepsilon_A\otimes\varepsilon_B)}\circ{\tt tens\_cofree\_str}_{A,B}$ and computing on promoted pure tensors as $m(x^!\otimes y^!)=(x\otimes y)^!$. It is a coalgebra morphism (`m_bang_is_coalg_mor`), which is precisely what makes the $\mathrm{EM}(!)$ product a coalgebra: for $P=(A,a)$ and $Q=(B,b)$ the product carrier is the **linear** tensor $A\otimes B$ and its structure map is
$$s \;=\; m_{A,B}\circ(a\otimes b)\;:\;A\otimes B\;\multimap\;{!(A\otimes B)},$$
i.e. `EM_prod_str`, with both coalgebra laws proved for *every* pair of coalgebras (`EM_prod_counit` from `der_m_bang`, `EM_prod_coassoc` from `m_bang_coassoc` + `m_bang_nat`). The terminal coalgebra `EM_term` is the `unit_cofree` of the previous entry. This is the answer to "what coalgebra does `EM_prod` carry?", the question the `EM_Cartesian` record leaves implicit and which the whole CBV = $\otimes$-product reading turns on.

> **Source — Melliès, *ibid.*, §7.4 / §6.10 (monoidal comonads).** *(Faithful paraphrase.)* A symmetric monoidal comonad on $(L,\otimes,1)$ is a comonad $!$ equipped with a natural comparison $m_{A,B}:{!A}\otimes{!B}\to{!(A\otimes B)}$ and a map $m_0:1\to{!1}$, coherent with the associator, unitors and symmetry, and compatible with $\varepsilon$ and $\delta$; such a comonad lifts the monoidal structure of $L$ to its Eilenberg–Moore category, the lifted tensor of $(A,a)$ and $(B,b)$ being $A\otimes B$ with structure map $m_{A,B}\circ(a\otimes b)$.

> **Difference.** The obvious definition of $m$ would go through a comparison $A\mathbin{\&}B\to A\otimes B$ between the cartesian and the linear product — which does not exist canonically in this model. The mechanisation sidesteps it entirely: it goes ${!A}\otimes{!B}\to{!({!A}\otimes{!B})}\to{!(A\otimes B)}$ using `tens_cofree_str` followed by ${!(\mathrm{der}\otimes\mathrm{der})}$, never $\mathbin{\&}\to\otimes$. Consequently `m_bang` is a *proved definition*, not a postulated comparison, and — unlike the naive promoted-point route — the two coalgebra laws of `EM_prod` hold on **every** pair of coalgebras rather than only on cofree ones, because their proofs run through the `m_bang` compatibility lemmas whose domain ${!A}\otimes{!B}$ *is* reducible by `tens_excl_charact`. `m_bang` is sealed (`Opaque`) once `m_bang_prom` is proved, so downstream proofs see only its pointwise law.

```coq
(* theories/cbv/em_cartesian.v *)
Definition m_bang (A B : ICone.type Ar) : icones_hom Ar (Bg A ⊗ Bg B) (Bg (A ⊗ B)).
Lemma m_bang_prom (A B : ICone.type Ar) (x : A) (y : B) :
  cone_norm x <= 1 -> cone_norm y <= 1 -> Lfun (m_bang A B) (x! ⊗p y!) = (x ⊗p y)!.
Lemma m_bang_is_coalg_mor (A B : ICone.type Ar) : _.
Definition EM_prod_str (P Q : Coalgebra Ar) : icones_hom Ar (coalg_obj P ⊗ coalg_obj Q) (Bg (coalg_obj P ⊗ coalg_obj Q)).
Definition EM_prod (P Q : Coalgebra Ar) : Coalgebra Ar.
Lemma EM_prod_obj (P Q : Coalgebra Ar) : coalg_obj (EM_prod P Q) = (coalg_obj P ⊗ coalg_obj Q).
Lemma EM_prod_str_E (P Q : Coalgebra Ar) : coalg_str (EM_prod P Q) = EM_prod_str P Q.
Definition EM_term : Coalgebra Ar.
```

### Melliès Prop 26 (`diagram81`)

Every $!$-coalgebra $(A,h_A)$ is a retract of its cofree coalgebra $(!A,\delta_A)$, via $A\xrightarrow{h_A}!A\xrightarrow{\varepsilon_A}A$. The formalisation records the key retraction square (Melliès' Eq (81)/(88)) as `diagram81`.

> **Source — Melliès, *Categorical Semantics of Linear Logic* (Panoramas et Synthèses 27, SMF 2009), Proposition 26.** In a linear category $L$, every coalgebra $(A, h_A)$ induces a retraction $A\xrightarrow{h_A}!A\xrightarrow{\varepsilon_A}A$ making the diagram $$\begin{array}{ccc} A & \xrightarrow{\;h_A\;} & !A\\[2pt] {\scriptstyle d_A}\downarrow & & \downarrow{\scriptstyle d_A}\\[2pt] A\otimes A & \xrightarrow{\;h_A\otimes h_A\;} & !A\otimes\,!A \end{array}$$ commute (with $\varepsilon_A\otimes\varepsilon_A$ the retraction of $h_A\otimes h_A$).

> **Difference.** Melliès states the square in a generic linear category; the mechanisation instantiates it at the icones comonad $!$ and records the concrete morphism equality `diagram81` (the transported diagonal via the structure map `coalg_str`), which the Cor-20 lift then consumes.

```coq
(* theories/cbv/em_cartesian.v *)
Lemma diagram81 (P : Coalgebra Ar) :
  icones_comp (tensor_mor (coalg_str P) (coalg_str P)) (coalg_d P) =
  icones_comp (d_bang (coalg_obj P)) (coalg_str P).
```

### Melliès Prop 20 (`coalg_mor_lift`)

The retraction-lifting property Melliès flags as *"less obvious"*: given a carrier retraction $r\circ i = \mathrm{id}$ with $i$ a coalgebra morphism, a map $f$ is a coalgebra morphism iff $i\circ f$ is. The formalisation mechanises the (66)/(67) diagram chase as `coalg_mor_lift`.

> **Source — Melliès, *ibid.*, §6.11 Proposition 20.** Suppose given a comonad $(K,\mu,\eta)$, two coalgebras $(A,h_A)$, $(B,h_B)$, and a retraction $A\xrightarrow{i}B\xrightarrow{r}A = \mathrm{id}_A$ between the underlying objects, with $i : (A,h_A)\to(B,h_B)$ a coalgebra morphism. Then, for every coalgebra $(X,h_X)$ and morphism $f : X\to A$, the following are equivalent: (i) $f$ is a coalgebra morphism $(X,h_X)\to(A,h_A)$; (ii) the composite $i\circ f$ is a coalgebra morphism $(X,h_X)\to(B,h_B)$.

> **Difference.** The REFERENCE MAP cites this as "Cor 20 / Prop 20"; in Melliès it is Proposition 20 of §6.11 (a lifting property of the coalgebra morphism $i$). The mechanisation gives the $(\Leftarrow)$ direction directly as `coalg_mor_lift` and applies it at the retraction $(h_A\otimes h_A)/(\varepsilon_A\otimes\varepsilon_A)$ to show the transported diagonal $d_A$ is a coalgebra morphism.

```coq
(* theories/cbv/em_cartesian.v *)
Lemma coalg_mor_lift (X PA QB : Coalgebra Ar)
    (i : icones_hom Ar (coalg_obj PA) (coalg_obj QB))
    (r : icones_hom Ar (coalg_obj QB) (coalg_obj PA))
    (f : icones_hom Ar (coalg_obj X) (coalg_obj PA)) :
  is_coalg_mor PA QB i ->
  icones_comp r i = icones_id Ar (coalg_obj PA) ->
  is_coalg_mor X QB (icones_comp i f) ->
  is_coalg_mor X PA f.
```

### Melliès Prop 27 (`transp_counitL`, `transp_counitR`, `transp_cocomm`, `transp_coassoc`)

A retract of a commutative comonoid inherits a commutative comonoid structure. The four transported laws (counit-left, counit-right, cocommutativity, coassociativity) are proved on a retract by a generic split-mono-cancellation transport plus associator/braiding/unitor naturality.

> **Source — Melliès, *ibid.*, Proposition 27.** Suppose that in a monoidal category $(C,\otimes,1)$ there is a retraction $A\xrightarrow{i}B\xrightarrow{r}A = \mathrm{id}_A$ between an object $A$ and a comonoid $(B, d_B, e_B)$. Then the following are equivalent: (i) $A$ lifts as a comonoid $(A, d_A, e_A)$ in such a way that $i : (A,d_A,e_A)\to(B,d_B,e_B)$ is a comonoid morphism; (ii) the diagram relating $d_B\circ i$ and $(i\otimes i)\circ (r\otimes r)\circ d_B\circ i$ (Melliès Eq (85)) commutes. When they hold, $(A, d_A, e_A)$ is uniquely determined.

> **Difference.** Melliès packages the transport as a single equivalence; the mechanisation unbundles it into the four comonoid-law equations (`transp_counitL/_R/_cocomm/_coassoc`) proved by a generic SMC transport under an Eq-(85) hypothesis fixing the $(i,r,d_B,e_B)$ retraction setup — the concrete content of "the comonoid $(A,d_A,e_A)$ is uniquely defined".

```coq
(* theories/cbv/em_cartesian.v *)
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
```

### Melliès Prop 28 (`EMComon_all`)

The analytic core: the comonoid predicate `EMComon` holds *unconditionally* on every coalgebra, discharging Melliès' flagged step that the transported diagonal and augmentation are coalgebra morphisms on an arbitrary carrier (not merely on promoted points).

> **Source — Melliès, *ibid.*, Proposition 28.** The monoidal structure inherited from a linear category $(L,\otimes,1)$ is cartesian in its category $L^{!}$ of Eilenberg–Moore coalgebras. (Proof: by Corollary 17, via Propositions 26 and 27, every coalgebra $(A,h_A)$ induces a comonoid $(A,d_A,e_A)$ with $d_A = (\varepsilon_A\otimes\varepsilon_A)\circ d_A^{!A}\circ h_A$ and $e_A = e_A^{!A}\circ h_A$ (Eq (88)); one checks $d_A$ and $e_A$ are coalgebra morphisms and monoidal natural.)

> **Difference.** The naïve route — reducing to *promoted points* $x^{!}$ — fails for a general carrier, since an arbitrary $a\,x$ is not promoted; the structural retraction proof (Prop 26 + Prop 27 + the Prop-20 lift) is what §7.4 actually requires. The headline is the single Prop `EMComon_all` asserting the comonoid predicate for *every* coalgebra $P$.

```coq
(* theories/cbv/em_cartesian.v *)
Lemma EMComon_all (P : Coalgebra Ar) : EMComon P.
```

### Comonoidality corollaries (`EMComon_cofree`, `EMComon_FMeas`)

Two named specialisations of the unconditional `EMComon_all`, kept as documented facts because they are what downstream code actually applies. `EMComon_cofree` says the cofree coalgebras $\tilde{!}B$ are comonoidal — the case Melliès' LC2 gives directly, and the base case of the retraction argument. `EMComon_FMeas` says the paper-Theorem-9.7 coalgebras $\mathsf{FMeas}(X)$ are comonoidal: this is the fact that makes every `tbase X` context *duplicable* in the CBV interpreter, i.e. that a measurable base type may be used more than once in a program without a linearity violation.

> **Source — Melliès, *ibid.*, Proposition 28.** The monoidal structure inherited from a linear category $(L,\otimes,1)$ is cartesian in its category $L^{!}$ of Eilenberg–Moore coalgebras. (Every coalgebra $(A,h_A)$ induces a comonoid $(A,d_A,e_A)$; in particular the cofree coalgebras and any distinguished family of coalgebras one names.)

> **Difference.** In an earlier state of the development these two families were the *only* coalgebras known to be comonoidal, each carrying its own bespoke witness; since `EMComon_all` they are one-line specialisations (`EMComon_all (bang_cofree B)`, `EMComon_all (FMeas_coalgebra X)`). They are retained under their own names purely as documentation and as stable entry points for the PPL layer — where `EMComon_FMeas` is the semantic content of "a base-type variable may be duplicated".

```coq
(* theories/cbv/em_cartesian.v *)
Definition EMComon_cofree (R : realType) (Ar : MeasSubcat R) (B : ICone.type Ar) : EMComon (bang_cofree B).
Definition EMComon_FMeas (R : realType) (Ar : MeasSubcat R) (X : ar_obj Ar) : EMComon (FMeas_coalgebra X).
```

### Melliès Cor 17 (`ICones_EM_cartesian`, `EM_Cartesian`)

The bridge from comonoids to a cartesian structure: a symmetric monoidal category in which every object carries a monoidal-natural comonoid is cartesian, with product carried by the tensor and terminal object the unit. The headline `ICones_EM_cartesian` bundles the full cartesian structure of $\mathrm{EM}(!)$ (product, terminal, projections, pairing, β-laws, terminal UP), the product being the linear $\otimes$.

> **Source — Melliès, *ibid.*, Corollary 17.** Let $(C,\otimes,1)$ be a symmetric monoidal category. The tensor product is a cartesian product and the tensor unit is a terminal object if and only if there exists a pair of monoidal natural transformations $d$ and $e$ with components $d_A : A\to A\otimes A$ and $e_A : A\to 1$ defining a comonoid $(A, d_A, e_A)$ for every object $A$.

> **Difference.** Melliès' Corollary 17 does *not* require the comonoids to be commutative; the underlying classical result is Fox's theorem (T. Fox, *Coalgebras and cartesian categories*, Comm. Algebra 4, 1976). The mechanisation records the cartesian package as the record `EM_Cartesian` and populates every field in `ICones_EM_cartesian`, with the binary product carried by the linear tensor $\otimes$ — not the cartesian $\&$.

```coq
(* theories/cbv/em_cartesian.v *)
Record EM_Cartesian (R : realType) (Ar : MeasSubcat R) : Type :=
  MkEMCartesian {
  cart_prod : Coalgebra Ar -> Coalgebra Ar -> Coalgebra Ar;
  cart_term : Coalgebra Ar;
  cart_prod_obj : forall P Q,
    coalg_obj (cart_prod P Q) = tensor Ar (coalg_obj P) (coalg_obj Q);
  cart_proj1 : forall P Q, icones_hom Ar (coalg_obj (cart_prod P Q)) (coalg_obj P);
  cart_proj2 : forall P Q, icones_hom Ar (coalg_obj (cart_prod P Q)) (coalg_obj Q);
  cart_pair : forall (Z P Q : Coalgebra Ar),
    coalg_hom Z P -> coalg_hom Z Q -> coalg_hom Z (cart_prod P Q);
  cart_beta1 : _; cart_beta2 : _;
  cart_term_mor : forall P, coalg_hom P cart_term;
  cart_term_unique : _;
}.

Definition ICones_EM_cartesian (R : realType) (Ar : MeasSubcat R) :
    EM_Cartesian Ar :=
  {| cart_prod := @EM_prod R Ar; cart_term := @EM_term R Ar;
     cart_prod_obj := @EM_prod_obj R Ar;
     cart_proj1 := @em_proj1_mor R Ar; cart_proj2 := @em_proj2_mor R Ar;
     cart_pair := fun Z P Q f g => @em_pair R Ar Z P Q f g;
     (* ... β-laws and terminal UP witnesses ... *) |}.
```

### EM product laws (`em_pair_mor`, `em_proj1_pair`, `em_proj2_pair`, `em_term_unique`)

The `EM_Cartesian` record of the previous entry lists `cart_beta1 : _`, `cart_beta2 : _` and `cart_term_unique : _` as elided fields; these are the witnesses. The pairing of $f:Z\to P$ and $g:Z\to Q$ is $\langle f,g\rangle=(f\otimes g)\circ d_Z$ — the transported comonoid diagonal of the *domain* followed by the bifunctor action (`em_pair_mor`, bundled as `em_pair`), and the projections are $\pi_1=\rho_P\circ(\mathrm{id}\otimes e_Q)$ and $\pi_2=\lambda_Q\circ(e_P\otimes\mathrm{id})$ (`em_proj1_mor` / `em_proj2_mor`) — the discarded factor is *erased by the comonoid counit*, which is where linearity is bought back. The $\beta$-laws `em_proj1_pair` / `em_proj2_pair` then follow from the counit laws `emc_counitR` / `emc_counitL` of $Z$ together with the comonoid-morphism identity `coalg_mor_e`. On the nullary side, `coalg_e P` is the canonical map into `EM_term` and `em_term_unique` shows it is the *only* coalgebra morphism there, because `coalg_e EM_term = id` (`coalg_e_term`).

> **Source — Melliès, *ibid.*, Corollary 17.** Let $(C,\otimes,1)$ be a symmetric monoidal category. The tensor product is a cartesian product and the tensor unit is a terminal object if and only if there exists a pair of monoidal natural transformations $d$ and $e$ with components $d_A:A\to A\otimes A$ and $e_A:A\to 1$ defining a comonoid $(A,d_A,e_A)$ for every object $A$.

> **Difference.** Corollary 17 asserts the *equivalence*; the mechanisation records the concrete data that equivalence produces, one equation per universal-property clause, and — this is the point — proves each of them for an **arbitrary** pair of coalgebras rather than for a chosen sub-class, since `EMComon_all` supplies the comonoid on every object. The $\beta$-laws are stated at the level of bare `icones_hom`s (with the coalgebra-morphism side condition of the *discarded* factor as an explicit hypothesis: `em_proj1_pair` needs `is_coalg_mor Z Q g`, `em_proj2_pair` needs `is_coalg_mor Z P f`), which is what lets them be reused for the bundled `coalg_hom` fields of `EM_Cartesian` without duplicating the chase.

```coq
(* theories/cbv/em_cartesian.v *)
Definition em_pair_mor (Z P Q : Coalgebra Ar)
    (f : icones_hom Ar (coalg_obj Z) (coalg_obj P))
    (g : icones_hom Ar (coalg_obj Z) (coalg_obj Q)) :
  icones_hom Ar (coalg_obj Z) (coalg_obj P ⊗ coalg_obj Q).
Definition em_proj1_mor (P Q : Coalgebra Ar) : icones_hom Ar (coalg_obj P ⊗ coalg_obj Q) (coalg_obj P).
Definition em_proj2_mor (P Q : Coalgebra Ar) : icones_hom Ar (coalg_obj P ⊗ coalg_obj Q) (coalg_obj Q).
Lemma em_proj1_pair (Z P Q : Coalgebra Ar) (f : _) (g : _) :
  is_coalg_mor Z Q g -> icones_comp (em_proj1_mor P Q) (em_pair_mor f g) = f.
Lemma em_proj2_pair (Z P Q : Coalgebra Ar) (f : _) (g : _) :
  is_coalg_mor Z P f -> icones_comp (em_proj2_mor P Q) (em_pair_mor f g) = g.
Lemma coalg_e_term : coalg_e (EM_term : Coalgebra Ar) = icones_id Ar (cone_one_car Ar).
Lemma em_term_unique (P : Coalgebra Ar) (h : _) : is_coalg_mor P EM_term h -> h = coalg_e P.
```

The general Cor-20 machinery these rest on is stated separately in
`em_cartesian.v`: the transported maps are coalgebra morphisms on **every**
coalgebra (`coalg_d_is_mor_gen`, `coalg_e_is_mor_gen`), every coalgebra
morphism is automatically a comonoid morphism (`coalg_mor_d`,
`coalg_mor_e`), and on a cofree object the transported maps collapse to the
LC2 ones (`coalg_d_cofree`, `coalg_e_cofree`, `EM_prod_str_cofree`) — the
bridge from the Melliès Prop 26 retraction to the general statement.

### Fox η-law cofree (`em_pair_mor_proj_id_cofree`)

The cartesian η-law $\langle\pi_1,\pi_2\rangle = \mathrm{id}$ on the cofree pair $(\tilde{!}A, \tilde{!}B)$: it reduces, via `tens_excl_charact`, to a computation on the promoted tensor $x^{!}\otimes y^{!}$. This is genuinely additional content beyond the β-laws.

> **Source — Fox, *Coalgebras and cartesian categories*, Comm. Algebra 4(7):665–667, 1976 (Fox's theorem).** *(Faithful paraphrase.)* A symmetric monoidal category is cartesian iff every object carries a (uniform, natural) cocommutative comonoid structure for which every morphism is a comonoid homomorphism; equivalently the category of cocommutative comonoids is the cartesian coreflection, with the tensor of comonoids serving as their categorical product. In particular the product's η-law $\langle\pi_1,\pi_2\rangle = \mathrm{id}$ holds, uniquely determined by the comonoid structure.

> **Difference.** The β-laws only give the universal property *out of* a coalgebra; the η-law is Fox's theorem specialised to $\mathrm{EM}(!)$ of a linear-exponential comonad (Melliès Prop 28 at the icones level). The cofree case `em_pair_mor_proj_id_cofree` establishes η on promoted tensors by Melliès' retract-and-lift technique, *not* by promoted-point reduction.

```coq
(* theories/cbv/cbv_adjunction.v *)
Lemma em_pair_mor_proj_id_cofree (A B : ICone.type Ar) :
  @em_pair_mor R Ar (EM_prod (bang_cofree A) (bang_cofree B))
    (bang_cofree A) (bang_cofree B)
    (em_proj1_mor (bang_cofree A) (bang_cofree B))
    (em_proj2_mor (bang_cofree A) (bang_cofree B))
  = icones_id Ar (coalg_obj (EM_prod (bang_cofree A) (bang_cofree B))).
```

### Fox η-law general (`em_pair_mor_proj_id`)

The full cartesian η-law $\langle\pi_1,\pi_2\rangle = \mathrm{id}$ for the $\mathrm{EM}(!)$ binary product on **every** pair of coalgebras, proved by the split-mono retraction $\mathrm{coalg\_str}\,P \otimes \mathrm{coalg\_str}\,Q \dashv \mathrm{der}_{cP}\otimes\mathrm{der}_{cQ}$ reducing the equation to the cofree case.

> **Source — Fox, *Coalgebras and cartesian categories*, Comm. Algebra 4(7):665–667, 1976.** *(Faithful paraphrase, as above.)* In a symmetric monoidal category whose objects all carry a uniform cocommutative comonoid, the tensor is the categorical product; hence for every pair the pairing $\langle\pi_1,\pi_2\rangle$ of the two projections equals the identity on the product object.

> **Difference.** Fox's theorem is stated for the whole comonoid category; the mechanisation specialises it to $\mathrm{EM}(!)$ and proves the η-law `em_pair_mor_proj_id` for every $(P,Q)$ by a split-mono retraction reducing to the cofree case above — Melliès' retract-and-lift, again avoiding promoted-point reduction.

```coq
(* theories/cbv/cbv_adjunction.v *)
Lemma em_pair_mor_proj_id (P Q : Coalgebra Ar) :
  @em_pair_mor R Ar (EM_prod P Q) P Q
    (em_proj1_mor P Q) (em_proj2_mor P Q)
  = icones_id Ar (tensor Ar (coalg_obj P) (coalg_obj Q)).
```

### Melliès Prop 29 (`CBV_Model`, `ICones_CBV`)

The cofree-coalgebra adjunction $U\dashv\tilde{!} : \mathbf{ICones}\rightleftarrows\mathrm{EM}(!)$ is a lax symmetric monoidal (linear/non-linear) adjunction. With Cor 20 in hand it is a genuine LNL adjunction with the **full** category of $!$-coalgebras as the cartesian value side. The `CBV_Model` record bundles every ingredient (the SMCC, the EM category, the cartesian value category, the $U/\tilde{!}$ actions, unit/counit/$\Phi$/$\Psi$/triangles, strict-monoidal $U$, lax symmetric monoidal $\tilde{!}$), all populated by `ICones_CBV`.

> **Source — Melliès, *Categorical Semantics of Linear Logic* (Panoramas et Synthèses 27, SMF 2009), Proposition 29.** Every linear category defines a linear-non-linear adjunction, and thus a model of intuitionistic linear logic. (The adjunction $L\dashv M$ between the symmetric monoidal category $L$ and its cartesian category $M \cong L^{!}$ of Eilenberg–Moore coalgebras is symmetric lax monoidal, and $! = L\circ M$ is the induced linear-exponential comonad.)

> **Difference.** Melliès obtains the monoidal adjunction via Lack's lifting theorem (S. Lack, *Composing PROPs*, Theory Appl. Categ. 13, 2004); the mechanisation packages the LNL structure as the record `CBV_Model` and discharges every field in `ICones_CBV`, taking the value side to be the *full* $\mathrm{EM}(!)$ (using Cor 20 / `em_pair_mor_proj_id`) rather than a chosen subcategory.

```coq
(* theories/cbv/cbv_adjunction.v *)
Record CBV_Model (R : realType) (Ar : MeasSubcat R) : Type := MkCBVModel {
  cbv_smcc : ICones_SMCC Ar;
  cbv_em   : EM_Cat Ar;
  cbv_cart : EM_Cartesian Ar;
  cbv_U_obj    : Coalgebra Ar -> ICone.type Ar;
  cbv_U_mor    : forall P Q, coalg_hom P Q -> icones_hom Ar (cbv_U_obj P) (cbv_U_obj Q);
  cbv_bang_obj : ICone.type Ar -> Coalgebra Ar;
  cbv_bang_mor : forall B C, icones_hom Ar B C -> coalg_hom (cbv_bang_obj B) (cbv_bang_obj C);
  cbv_unit     : forall P, coalg_hom P (cbv_bang_obj (cbv_U_obj P));
  cbv_counit   : forall B, icones_hom Ar (cbv_U_obj (cbv_bang_obj B)) B;
  cbv_phi : forall P B, coalg_hom P (cbv_bang_obj B) -> icones_hom Ar (cbv_U_obj P) B;
  cbv_psi : forall P B, icones_hom Ar (cbv_U_obj P) B -> coalg_hom P (cbv_bang_obj B);
  cbv_phiK : _; cbv_psiK : _; cbv_triangleL : _; cbv_triangleR : _;
  cbv_U_prod : forall P Q, cbv_U_obj (cart_prod cbv_cart P Q) =
                            tensor Ar (cbv_U_obj P) (cbv_U_obj Q);
  cbv_U_term : cbv_U_obj (cart_term cbv_cart) = cone_one_car Ar;
  (* !̃ lax symmetric monoidal: m2 / m0 comparisons, lax coherence,
     counit-monoidality *)
  cbv_lax_assoc : _; cbv_lax_braid : _;
  cbv_counit_monoidal2 : _; cbv_counit_monoidal0 : _;
}.

Definition ICones_CBV (R : realType) (Ar : MeasSubcat R) : CBV_Model Ar :=
  {| cbv_smcc := ICones_smcc Ar; cbv_em := ICones_EM Ar;
     cbv_cart := ICones_EM_cartesian Ar;
     cbv_U_obj := @U_obj R Ar; cbv_U_mor := @U_mor R Ar;
     (* ... !̃ / unit / counit / triangle / lax-monoidal witnesses ... *) |}.
```

### Lax coherence of m (`m_bang_assoc`, `m_bang_lunit`, `m_bang_runit`, `m_bang_braid`, `bang_m`, `bang_e0`, `adj_counit_monoidal2`)

The `CBV_Model` record of the previous entry carries `cbv_lax_assoc : _`, `cbv_lax_braid : _`, `cbv_counit_monoidal2 : _` and `cbv_counit_monoidal0 : _` as elided fields; these are the proofs behind them, and they are the one block of genuinely new content in the LNL assembly. $(!,m,e_0)$ is a **lax symmetric monoidal** endofunctor of $(\otimes,1)$: `m_bang_assoc` is the associativity hexagon ${!\alpha}\circ m_{A\otimes B,C}\circ(m_{A,B}\otimes\mathrm{id}) = m_{A,B\otimes C}\circ(\mathrm{id}\otimes m_{B,C})\circ\alpha$; `m_bang_braid` is the symmetry ${!\sigma}\circ m_{A,B}=m_{B,A}\circ\sigma$; and `m_bang_lunit` / `m_bang_runit` are the two unitors, phrased against the transported unit comparison `unit_cofree_str`. Each is discharged by the standing recipe — reduce by `tens_excl_charact` (or its ternary form `tens_excl_charact3l`, and the unit forms `tens_excl_unitL` / `tens_excl_unitR`) to agreement on promoted pure tensors, then compute with `m_bang_prom` and the structural-iso `…Ep` laws. Packaged at the $\mathrm{EM}(!)$ level, the binary comparison is the coalgebra morphism `bang_m` $:\ {\tt EM\_prod}\,\tilde{!}A\,\tilde{!}B\to\tilde{!}(A\otimes B)$ and the nullary one is `bang_e0` $:\ {\tt EM\_term}\to\tilde{!}1$; the monoidality of the counit is `adj_counit_monoidal2` (= `der_m_bang`) and `adj_counit_monoidal0` (= `unit_cofree_counit`).

> **Source — Melliès, *Categorical Semantics of Linear Logic* (Panoramas et Synthèses 27, SMF 2009), §6.10 (monoidal comonads and monoidal adjunctions) and Proposition 29.** *(Faithful paraphrase.)* A comonad is *symmetric monoidal* when it is equipped with comparison maps $m_{A,B}:{!A}\otimes{!B}\to{!(A\otimes B)}$ and $m_0:1\to{!1}$ that are natural, coherent with the associator, the unitors and the symmetry, and compatible with the counit $\varepsilon$ and the comultiplication $\delta$; for such a comonad the Eilenberg–Moore adjunction is a monoidal adjunction — the forgetful functor is strong monoidal, the cofree functor lax monoidal, and the unit and counit are monoidal natural transformations. Every linear category therefore defines a linear/non-linear adjunction (Proposition 29).

> **Difference (why two of the eight witnesses sit outside the record).** Melliès' statement bundles all four monoidality squares. The mechanisation records only the *counit* ones inside `CBV_Model`: the two **unit** laws `adj_unit_monoidal2` and `adj_unit_monoidal0` are **definitional** — $m_{UP,UQ}\circ(\eta_P\otimes\eta_Q)$ *is* the structure map of the product coalgebra (`EM_prod_str_E`), and $\eta_{\tt EM\_term}$ *is* `unit_cofree_str` — so stating them as record fields would only add dependent-type plumbing (the field types would have to mention `cart_prod_obj`'s carrier equality) for no content. They are kept as standalone lemmas instead. For the same reason $U$ is **strict**, not merely strong, monoidal: the product and terminal *carriers* are literally $\otimes$ and $1$ (`cbv_U_prod`, `cbv_U_term` are equalities, not comparisons), so its structure maps are identities. Finally, the $\mathrm{EM}(!)$-level associator / unitors / braiding are the coalgebra morphisms whose underlying maps are `tensor_assoc` / `tensor_lunit` / `tensor_runit` / `tensor_braid`, so the lax diagrams project through the faithful $U$ onto the `m_bang_*` equations — the record's fields are those projections.

```coq
(* theories/cbv/cbv_adjunction.v *)
Lemma m_bang_assoc (A B C : ICone.type Ar) : _.
Lemma m_bang_braid (A B : ICone.type Ar) :
  icones_comp (bang_fmap (iso_fwd (tensor_braid A B))) (m_bang A B) =
  icones_comp (m_bang B A) (iso_fwd (tensor_braid (Bg A) (Bg B))).
Lemma m_bang_lunit (A : ICone.type Ar) : _.
Lemma m_bang_runit (A : ICone.type Ar) : _.
Definition bang_m (A B : ICone.type Ar) :
  coalg_hom (EM_prod (bang_cofree A) (bang_cofree B)) (bang_cofree (A ⊗ B)).
Definition bang_e0 : coalg_hom (EM_term : Coalgebra Ar) (bang_cofree (cone_one_car Ar)).
Lemma adj_counit_monoidal2 (A B : ICone.type Ar) :
  icones_comp (adj_counit (A ⊗ B)) (m_bang A B) = tensor_mor (adj_counit A) (adj_counit B).
Lemma adj_counit_monoidal0 :
  icones_comp (adj_counit (cone_one_car Ar)) unit_cofree_str = icones_id Ar (cone_one_car Ar).
Lemma adj_unit_monoidal2 (P Q : Coalgebra Ar) :
  icones_comp (m_bang (coalg_obj P) (coalg_obj Q)) (tensor_mor (coalg_str P) (coalg_str Q)) =
  coalg_str (EM_prod P Q).
Lemma adj_unit_monoidal0 : coalg_str (EM_term : Coalgebra Ar) = unit_cofree_str.
```

### FMeas lax monoidal (`fmeas_lax`, `fmeas_lax_E`, `fmeas_lax_dirac`, `int_to_linhom_pres_path_in_cone`)

Paper Theorem 9.7 makes $\mathsf{FMeas}$ a *functor* $\mathbf{Ar}\to\mathbf{ICones}^{!}$; it never equips that functor with a monoidal comparison. This entry supplies one. For all $X,Y\in\mathbf{Ar}$ there is an $\mathbf{ICones}$ morphism
$${\tt fmeas\_lax}\,X\,Y\;:\;\mathsf{FMeas}(X)\otimes\mathsf{FMeas}(Y)\;\multimap\;\mathsf{FMeas}(X\times Y)$$
sending the pure tensor $\mu\otimes\nu$ to the cartesian product measure (`fmeas_lax_E`, with the function-level product `fmeas_lax_pre` = the pushforward of $\mu\times_{\mathrm{meas}}\nu$ along the carrier cast `ar_prod_cast`, canonicalised to vanish off the $\sigma$-algebra), and hence Dirac masses to the Dirac at the paired point, $\delta_x\otimes\delta_y\mapsto\delta_{(x,y)}$ (`fmeas_lax_dirac`) — the computational content the PPL layer consumes for `kernel_lift2` and the binary arithmetic clauses. The construction is `tensor_uncurry` of an outer linear hom $\mathsf{FMeas}(X)\multimap(\mathsf{FMeas}(Y)\multimap\mathsf{FMeas}(X\times Y))$ obtained by applying paper Thm 6.1 (`int_to_linhom`) **twice**: inner, at the Dirac-pushforward path `dirac_lax` $:\ y\mapsto\delta_{(x,y)}$; outer, at the path-of-paths $x\mapsto{\tt fmeas\_lax\_pre\_at\_dirac}\,x$, which lands in the iCone of linear homs. `fmeas_lax_E` reduces on the pure tensor to the load-bearing Pettis/Tonelli identity `fmeas_lax_pre_iterated`, which expresses the pushed-forward product on a measurable $U$ as the iterated icone-integral of `dirac_lax`.

That outer application is exactly the paper-§6 follow-up to Theorem 6.1 that `bilin.v` previously flagged as deferred — *path preservation in the cone variable* — and it is now discharged as `int_to_linhom_pres_path_in_cone`: for a measurable path $\eta$ of the iCone $\mathsf{Path}(X,B)$, the assignment $r\mapsto\mathcal{I}^{B}_{X}(\eta\,r)$ is a measurable path of $\mathsf{FMeas}(X)\multimap B$. This is an *independently-indexed joint-measurability* statement: the measure varies in the test arity $Z$ (through the `path_car Ar Z (FMeas X)` that parameterises the internal-hom test) while the integrand path varies in $Y$ (through $\eta$). It is proved by packaging both into the joint state $\mathbf{Ar}(Z)\times\mathbf{Ar}(Y)$ of `icone_integral_joint_measurable` and specialising along the diagonal $(z,r)\mapsto(z,(z,r))$.

> **Paper — Theorem 9.7** (arXiv 2212.02371, `th:meas-cone-coalgebra-stab`). Equipped with $\mathsf{h}_X$, the object $\mathsf{FMeas}(X)$ of $\mathbf{ICones}$ is a coalgebra of the comonad ${!}\_$. Moreover for each $\phi\in\mathbf{Ar}(X,Y)$, we have $\mathsf{FMeas}(\phi)=\phi_\ast\in\mathbf{ICones}^!(\mathsf{FMeas}(X),\mathsf{FMeas}(Y))$ so that $\mathsf{FMeas}$ is a functor $\mathbf{Ar}\to\mathbf{ICones}^!$.

> **Paper — Theorem 6.1** (arXiv 2212.02371, `th:meas-path-equiv`). For each $X\in\mathbf{Ar}$ and integrable cone $B$, one has $\mathcal{I}^{B}_X\in\mathbf{ICones}(\mathsf{Path}(X,B),\mathsf{FMeas}(X)\multimap B)$ and $\mathcal{I}^{B}_X$ is an isomorphism which is natural in $X$ and in $B$ (between functors $\mathbf{Ar}^{\mathsf{op}}\times\mathbf{ICones}\to\mathbf{ICones}$).

> **Difference.** The paper stops at *functoriality* of $\mathsf{FMeas}$; the lax monoidal comparison is beyond it, and it is not formal bookkeeping — `fmeas_lax` is where Fubini–Tonelli enters the categorical layer. Two encoding points. (i) The codomain carrier is the *cartesian* product $(\mathsf{ar\_carrier}\,X\times\mathsf{ar\_carrier}\,Y)$, whereas the object $X\times Y$ of $\mathbf{Ar}$ carries only a propositional carrier equality; every statement therefore transports along `ar_prod_cast`, whose measurability is the `MeasSubcat` field `ar_prod_cast_meas`. (ii) The entry closes a previously-deferred obligation rather than adding a new axiom: `int_to_linhom_pres_path_in_cone` is proved, not assumed. What remains deferred on that front is stated in `bilin.v` and unchanged here — upgrading the Thm 6.1 `cones_iso` to an `mcones_iso` / `icones_iso` still needs the symmetric `linhom_to_int` side (a `dirac_path`-pushforward test that is not yet available) and integral-preservation in the cone variable.

```coq
(* theories/cbv/fmeas_lax.v *)
Definition fmeas_lax_pre : _.
Definition dirac_lax (x : ar_carrier Ar X) : path_car Ar Y (fmeas R (ar_carrier Ar (ar_prod Ar X Y))).
Definition fmeas_lax : icones_hom Ar (tensor Ar (fmeas R (ar_carrier Ar X)) (fmeas R (ar_carrier Ar Y)))
                                     (fmeas R (ar_carrier Ar (ar_prod Ar X Y))).
Lemma fmeas_lax_pre_iterated (µ : _) (ν : _) (U : set (ar_carrier Ar (ar_prod Ar X Y))) : _.
Lemma fmeas_lax_E (µ : _) (ν : _) : Lfun (fmeas_lax X Y) (ptensor µ ν) = fmeas_lax_pre µ ν.
Lemma fmeas_lax_dirac (x : ar_carrier Ar X) (y : ar_carrier Ar Y) : _.
```

```coq
(* theories/homs/bilin.v *)
Lemma int_to_linhom_pres_path_in_cone (Y : ar_obj Ar) (η : ar_carrier Ar Y -> path_car Ar X B) :
  is_measurable_path η ->
  is_measurable_path (Ar:=Ar) (C:=linhom_car Ar (fmeas R (ar_carrier Ar X)) B)
    (fun r => int_to_linhom (η r)).
```

```coq
(* theories/icones/icone_integral.v *)
Lemma icone_integral_joint_measurable : _.
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
echo 'From Icones.exp Require Import seely. Print Assumptions Icones.exp.seely.ICones_Seely.' \
  | rocq top -Q theories Icones

# Or for the rejection-sampling master theorem:
echo 'From Icones.programs Require Import ex_reject_model. Print Assumptions Icones.programs.ex_reject_model.reject_model_master.' \
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
   logic core: $(\mathbf{ICones}, \otimes, \mathbf{1})$ is a SMCC.
3. **Theorem 7.32** (`SCones_ccc` in `theories/stable/scones_ccc.v`) — the
   cartesian closed `SCones`.
4. **Theorem 9.5** (`ICones_Seely` in `theories/exp/seely.v`) — the Seely
   category structure (the full LL / intuitionistic-linear model).
5. **Theorem 9.7** (`FMeas_coalgebra` in `theories/exp/coalgebra.v`) — the
   measure cone is a `!`-coalgebra; `X ↦ FMeas(X)` is a functor into `EM(!)`.
6. **The mechanised paper-cited meta-theorems** (`EMComon_all` and
   `ICones_CBV` in `theories/cbv/em_cartesian.v` /
   `theories/cbv/cbv_adjunction.v`) — Mellies' Cor 20 (full
   cartesianness of `EM(!)`) and the LNL adjunction.

For the PPL development on top — including recursive examples and their
mass identities — see the [PPL tab](../ppl/). For the dependency structure
of the formalisation itself — which result rests on which — see the
[Graph tab](../graph.html).
