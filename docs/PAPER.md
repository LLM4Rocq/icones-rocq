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
| Lem 2.9 | Addition and scalar multiplication on a cone are increasing and $\omega$-continuous. | `addr_omega_continuous`, `addl_omega_continuous`, `scaler_omega_continuous` — `theories/cones/basic_lemmas.v` |
| Lem 2.8 / 2.10 | $\omega$-continuity of the inverse of a bijective linear continuous map / of the difference $g - f$ of an increasing $f$ below an $\omega$-continuous $g$. | `invf_omega_continuous`, `diff_omega_continuous` — `theories/cones/basic_lemmas.v` |
| Lem 2.11 | A linear map is bounded on the unit ball; the operator norm $\lVert f\rVert$. | `linmap_bounded`, `linmap_norm` — `theories/cones/basic_lemmas.v` |
| Thm 2.18 | $\mathbf{Cones}$ has all small products $\mathop{\&}_{i\in I}P_i$ (terminal object $\top$ at $I=\emptyset$). | `cones_prod`, `cones_proj`, `cones_tuple` — `theories/cones/cone_cat.v` |
| Lem 2.19 | Separate $\omega$-continuity implies joint $\omega$-continuity (diagonal-collapse form). | `diagonal_collapse` — `theories/cones/cone_cat.v` |
| Thm 2.20 | $\mathbf{Cones}$ has all binary equalisers, hence is complete; the inclusion reflects the order. | `cones_eq`, `cones_eq_incl`, `cones_eq_med` — `theories/cones/cone_cat.v` |
| Lem 2.21 / Prop 2.22 | An iso in $\mathbf{Cones}$ preserves the norm exactly (constructive form of $\lVert f\rVert=1$). | `cones_iso_preserves_norm` — `theories/cones/cone_cat.v` |
| Lem 2.23 | Transport of a cone structure along a bijection. | `transport_isPrecone` — `theories/cones/cone_cat.v` |

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

> **Difference.** Because the operator-norm value $\lVert f\rVert$ is not materialised in the `cones_hom_norm_le1` encoding (it is only introduced as *a* bound in Lemma 2.11), the paper's chain 2.21 $\to$ 2.22 is restated as exact pointwise norm preservation for a two-sided-invertible morphism: if $f$ has an inverse $g$ in $\mathbf{Cones}$ (with $g\circ f=\mathrm{id}$ and $f\circ g=\mathrm{id}$) then $\lVert f(x)\rVert=\lVert x\rVert$ for all $x$. This is the constructively usable content of $\lVert f\rVert=1$ (see `cone_cat.v:1349-1357`); it drops the $P\neq 0$ hypothesis, which is needed only to name the numeric value.

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

> **Difference.** The mechanisation establishes *existence* of the transported **precone** structure only — `transport_isPrecone : isPrecone R S`, built from `trans_add`/`trans_scale`/`trans_norm` and the twelve `trans_*` axiom lemmas. Packaging the full `HB.instance` of the cone (with the norm axioms) is deferred as a downstream task and re-stated per target file when needed concretely (see the note at `cone_cat.v:1473-1478`); uniqueness is exactly the observation that every transported axiom is determined by $f$.

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

### Lem 3.17 (`fmeas_push`)

Push-forward of measures along $\phi\in\mathbf{Ar}(X,Y)$ is a $\mathbf{Cones}$-morphism $\mathsf{FMeas}(X)\to\mathsf{FMeas}(Y)$, and the operation $\mathsf{FMeas}$ extends to a functor $\mathbf{Ar}\to\mathbf{MCones}$ acting on morphisms by push-forward, $\mathsf{FMeas}(\phi)=\phi_*$. The packaged morphism is `fmeas_push`; functoriality is witnessed by `fmeas_push_id` and `fmeas_push_comp`.

> **Paper — Lemma 3.17** (arXiv 2212.02371, `lemma:pushf-measurable`). We have $\phi_*\in\mathbf{MCones}(\mathsf{FMeas}(X),\mathsf{FMeas}(Y))$. The operation $\mathsf{FMeas}$ on measurable cones extends to a functor $\mathsf{FMeas}:\mathbf{Ar}\to\mathbf{MCones}$, acting on morphisms by measure push-forward: $\mathsf{FMeas}(\phi)=\phi_*$.

> **Difference.** The mechanisation packages $\phi_*$ as a `cones_hom` (a linear, $\omega$-continuous map of norm $\le 1$) rather than as a full `mcones_hom` record: path-preservation is not bundled at this point. The packaged mcones/icones-morphism version, `FMeas_fmap`, lives later in `theories/homs/coalgebra.v` for the ICones/coalgebra layer. Functoriality is stated on the underlying functions ($=1$) — `fmeas_push_id` and `fmeas_push_comp` — rather than as categorical equalities.

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
| Lem 4.7 | The integration operator $\mathcal{I}^{B}_X$ is bilinear (separately linear in the path and the measure), continuous and measurable. | `icone_integral_*` family + `bilin.v` — `theories/icones/icone_integral.v`, `theories/homs/bilin.v` |
| Thm 4.12 | The cone of paths $\mathsf{Path}(X,B)$ into an integrable cone is itself an `ICone`. | the anonymous `isICone` instance built from `path_int_exists` — `theories/icones/examples_icone.v` |
| Thm 4.5 | $\mathsf{FMeas}(X)$ is integrable; the unit cone $1=\perp$ likewise. | `FMeas` is an `ICone`; the `isICone` instance on `cone_one_car Ar` — `theories/icones/examples_icone.v` |
| Cat 4 | The category $\mathbf{ICones}$ has integrable cones and $\mathbf{MCones}$-morphisms preserving the integral. | `icones_hom`, `icones_comp`, `ICones` — `theories/icones/icone_cat.v` |
| Thm 4.15 (Fubini) | The two iterated integrals of a path of paths coincide: $\int_X(\int_Y\dots)\,d\mu = \int_Y(\int_X\dots)\,d\nu$. | `fubini_cone_eq` (paper-form wrapper `fubini_cone_eq_arprod`); supporting `fubini_path_X`/`fubini_path_Y`, `fubini_iter_fun_X` — `theories/icones/fubini.v` |
| Thm 4.16 (ICones complete) | $\mathbf{ICones}$ is complete: it has all small products and all binary equalisers, each with its universal property. | `icones_tuple_unique`, `icones_eq_med_unique` (with `icones_prod`/`icones_eq`, `icones_proj`, `icones_tuple`, `icones_eq_incl`, `icones_eq_med`) — `theories/icones/icone_cat.v` |
| Thm 4.18 | $\mathbf{ICones}$ is well-powered and $1$ is both a separator and a coseparator. | `icones_coseparator`, `icones_separator` — `theories/icones/icone_cat.v`; `icones_well_powered`, `icones_subobject_classP` — `theories/icones/representable.v` |
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

### Thm 4.15 Fubini (`fubini_cone_eq`)

The Fubini theorem for cones: the two iterated integrals of a path of paths coincide in $B$. Integrating $\beta$ first over $X$ against $\mu$ and then over $Y$ against $\nu$ yields the same element of $B$ as integrating first over $Y$ against $\nu$ and then over $X$ against $\mu$. The headline identity is `fubini_cone_eq`; the paper-form wrapper `fubini_cone_eq_arprod` takes a genuine measurable path $\beta$ on the product arity $X\times Y$.

> **Paper — Theorem 4.15** (arXiv 2212.02371, `th:paths-Fubini`). Let $X,Y\in\mathbf{Ar}$, $\eta\in\underline{\mathsf{Path}(X,\mathsf{Path}(Y,B))}$, $\mu\in\underline{\mathsf{FMeas}(X)}$ and $\nu\in\underline{\mathsf{FMeas}(Y)}$. We have $$\int_Y\Big(\int_X\eta(r)\mu(dr)\Big)(s)\,\nu(ds)=\int_{X\times Y}\mathsf{fl}(\eta)(t)\,(\mu\times\nu)(dt).$$

> **Difference.** Because the `ar_prod_carrier_eq` cast into the product arity is not transparent in the formalization, `fubini_cone_eq` states the equation cast-free, directly between the two iterations for $\beta : X\times Y\to B$ (via the iterated paths `fubini_path_X`/`fubini_path_Y`), rather than routing through the bridging product integral $\int_{X\times Y}\mathsf{fl}(\eta)\,d(\mu\times\nu)$. The proof goes through the scalar Tonelli lemmas (`fubini_tonelli1`/`fubini_tonelli2`) on each arity-$0$ test and promotes to $B$ by separation (`mcone_M_sep`). The paper-form statement, for a measurable path $\beta$ on the product arity, is the wrapper `fubini_cone_eq_arprod`, which discharges the five hypotheses of `fubini_cone_eq` from `is_measurable_path β` via the cast-measurability helpers. The inner-integral apparatus `fubini_iter_fun_X` (with `fubini_iter_fun_X_norm_le` bounding its norm by Lemma 4.2 and `fubini_iter_fun_X_is_path` proving it is a measurable path) supports `fubini_path_X`.

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

In $\mathbf{ICones}$ the unit cone $1$ is both a separator and a coseparator, and the category is well-powered. All three conjuncts are formalized: `icones_coseparator` records that $1$ is a coseparator (two morphisms agree iff every arity-$0$ test of the codomain agrees on their images at every point), `icones_separator` records that $1$ is a separator (two morphisms agree iff they agree at every point), and `icones_well_powered` discharges well-poweredness by exhibiting a small classifying `Type` (`SubobjClassifier`) into which subobjects inject up to iso (`icones_subobject_classP`).

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
| Lem 5.3 | Argument-swapping iso $\mathsf{sw}$ across a path: $f\mapsto\lambda r.\lambda x.\,f(x)(r)$ (the path-preservation core is packaged). | `swap_lin_path` — `theories/homs/tensor_hom_iso.v` |
| Lem 5.4 / Def 5.7 | The internal hom $C\multimap D$ carrier (the integrable cone of $\mathbf{ICones}$-morphisms $C\to D$); its action $(h\multimap g):(C_1\multimap D_1)\to(C_2\multimap D_2)$ by $(h\multimap g)(f)=g\circ f\circ h$. | `linhom_car`, `linhom_postc`, `linhom_prec`, `linhom_map_fun` — `theories/homs/linhom.v` |
| Lem 5.5 | Argument-swapping natural iso $\mathsf{sw}':B_1\multimap(B_2\multimap C)\to B_2\multimap(B_1\multimap C)$, $f\mapsto\lambda x_1.\lambda x_2.\,f(x_1)(x_2)$. | `swap_lin_lin_hom` — `theories/homs/tensor_iso.v` |
| Def 5.6 | The cone of integrable bilinear maps $(C_1,C_2)\multimap D=C_1\multimap(C_2\multimap D)$. | `bilin_data`, `bilin_to_curried`, `curried_to_bilin` — `theories/homs/linhom.v` |
| Prop 5.8 | The internal-hom action $h\multimap g$ lifts to an $\mathbf{ICones}$ morphism. | `linhom_map_icones` — `theories/homs/linhom_functor.v` |
| Thm 5.9 | The functor $C\multimap{-}$ preserves all limits (hence has a left adjoint). | `limpl_preserves_prod`, `limpl_preserves_limits` — `theories/homs/limpl_continuous.v` |
| Lem 5.10 | Swap of the two hom-arguments across a path: $f\mapsto\lambda(y,r,x).\,f(x,r,y)$. | `lfun_path_swap` — `theories/homs/tensor_iso.v` |
| Lem 5.11 | A bounded $\eta:X\to(B\otimes C)\multimap 1$ is a path once its pure-tensor evaluations are measurable. | `path_tens_to_one`, `path_tens_to_one_unit` — `theories/homs/tensor_iso.v` |
| Thm 5.12 | The currying isomorphism $(B\otimes C)\multimap D\;\simeq\;B\multimap(C\multimap D)$. | `tensor_hom_iso` — `theories/homs/tensor_iso.v` |
| Thm 5.13 | Norm identity for pure tensors: $\lVert x\otimes y\rVert=\lVert x\rVert\,\lVert y\rVert$. | `tensor_norm_le` ($\le$) + the $\ge$ direction via Prop 3.11 — `theories/homs/tensor.v` / `tensor_iso.v` |
| Prop 5.14 | A morphism out of an iterated tensor is determined on pure tensors $x\otimes y$. | `tensor_ext`, `tensor_ext3`, `tensor_ext4` — `theories/homs/tensor.v`, `theories/homs/smcc.v` |
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

### Lem 5.10 (`lfun_path_swap`)

Swapping the two hom-arguments across a path: from $f\in\mathbf{ICones}(B,\mathrm{Path}(X,C\multimap D))$ one obtains $f'=\lambda(y,r,x).\,f(x,r,y)\in\mathbf{ICones}(C,\mathrm{Path}(X,B\multimap D))$. This is the key ingredient of the tensor–hom iso (used by `path_tens_to_one`).

> **Paper — Lemma 5.10** (arXiv 2212.02371, `lemma:lfun-path-swap`). Let $X\in\mathbf{AR}$ and let $B,C,D$ be measurable cones. Let $f$ be an element of $\mathbf{ICones}(B,\mathrm{Path}(X,C\multimap D))$. Then $f'=\lambda(y,r,x).\,f(x,r,y)$ belongs to $\mathbf{ICones}(C,\mathrm{Path}(X,B\multimap D))$.

```coq
(* theories/homs/tensor_iso.v — Section LfunPathSwap,
   Variables (R : realType) (Ar : MeasSubcat R), (X : ar_obj Ar),
   (B C D : ICone.type Ar),
   f : icones_hom Ar B (path_car Ar X (linhom_car Ar C D)),
   Local Notation PBD := (path_car Ar X (linhom_car Ar B D)) *)
Definition lfun_path_swap : icones_hom Ar C PBD :=
  MkIConesHom lfps_mcones lfps_mcones_pres_int.

Lemma lfun_path_swapE (y : C) (r : ar_carrier Ar X) (x : B) :
  linhom_fun (path_fun (lfun_path_swap y) r) x =
  linhom_fun (path_fun (f x) r) y.
```

### Lem 5.11 (`path_tens_to_one`, `path_tens_to_one_unit`)

A candidate path $\eta:X\to(B\otimes C)\multimap 1$ is genuinely a measurable path as soon as it is bounded and its pure-tensor evaluations are jointly measurable. This is the key observation behind the measurability of the tensor–hom iso $\Psi$ (Thm 5.12).

> **Paper — Lemma 5.11** (arXiv 2212.02371, `lemma:path-tens-to-one`). Let $X\in\mathbf{AR}$ and $B,C$ be integrable cones. Let $\eta:X\to\underline{(B\otimes C)\multimap 1}$ be a function. One has $\eta\in\underline{\mathrm{Path}(X,(B\otimes C)\multimap 1)}$ as soon as (i) $\eta(X)\subseteq\underline{(B\otimes C)\multimap 1}$ is bounded, and (ii) for all $Y\in\mathbf{AR}$, $\beta\in\underline{\mathrm{Path}(Y,B)}$ and $\gamma\in\underline{\mathrm{Path}(Y,C)}$, the function $\lambda(s,r)\in Y\times X.\ \eta(r)(\beta(s)\otimes\gamma(s)):Y\times X\to\mathbb{R}_{\geq 0}$ is measurable.

> **Difference.** The two hypotheses `ηbound` ($\eta$ is bounded) and `ηpt` (the pure-tensor evaluation $\lambda s.\,\eta(\varphi\,s)(\beta\,s\otimes\gamma\,s)$ is measurable) match the paper's two bullet conditions. The mechanisation factors the norm-$\le 1$ case as `path_tens_to_one_unit`; the general bounded case (`path_tens_to_one`) rescales $\eta$ into the unit ball and applies it.

```coq
(* theories/homs/tensor_iso.v — Section PathTensToOneGen,
   Variables (R : realType) (Ar : MeasSubcat R), (B C : ICone.type Ar),
   (X : ar_obj Ar), Local Notation BC := (tensor B C),
   η : ar_carrier Ar X -> linhom_car Ar BC (cone_one_car Ar),
   ηbound : exists M : R, forall r, cone_norm (η r) <= M,
   ηpt : (* pure-tensor evaluations are measurable *) _ *)
Lemma path_tens_to_one : is_measurable_path η.

(* norm-≤1 case (Section PathTensToOne, hypothesis Hη1 : cone_norm (η r) <= 1) *)
Lemma path_tens_to_one_unit : is_measurable_path η.
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
| Thm 6.2 | *Dirac density*: two $\mathbf{ICones}$ morphisms $\mathsf{FMeas}(X) \to B$ that agree on every Dirac mass $\boldsymbol\delta^{X}(r)$ are equal. | `dirac_dense` — `theories/homs/coalgebra.v` |
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

### Thm 6.2 (`dirac_dense`)

The Dirac masses $\boldsymbol\delta^{X}(r)$ are *dense* in the integrable cone $\mathsf{FMeas}(X)$: any two $\mathbf{ICones}$ morphisms out of $\mathsf{FMeas}(X)$ that agree on every $\boldsymbol\delta^{X}(r)$ coincide. This is the proof engine behind the coalgebra structure of $\mathsf{FMeas}(X)$ and the embedding of $\mathbf{Skern}$; it is a consequence of the path–hom bijection $\mathcal{I}^{B}_X$ of Thm 6.1. Here `Lfun h` is the underlying linear function $\mathsf{cones\_hom\_fun}(\mathsf{mcones\_hom\_cones}(\mathsf{icones\_hom\_mcones}\,h))$ of an `icones_hom`, `dirac_fmeas r` is the Dirac measure $\boldsymbol\delta^{X}(r)\in\mathsf{FMeas}(X)$, and `FMeas X` is $\mathsf{fmeas}\,R\,(\mathsf{ar\_carrier}\,\mathrm{Ar}\,X)$.

> **Paper — Theorem 6.2** (arXiv 2212.02371, `th:dirac-dense`). Let $X\in\mathbf{Ar}$, $B$ be an object of $\mathbf{ICones}$ and $f_1,f_2\in\mathbf{ICones}(\mathsf{FMeas}(X),B)$. If, for all $r\in X$, one has $f_1(\boldsymbol\delta^{X}(r))=f_2(\boldsymbol\delta^{X}(r))$ then $f_1=f_2$.

```coq
(* theories/homs/coalgebra.v — Section Coalgebra, Variables R Ar *)
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

---

## Paper § 7 — Stable functions and the cartesian-closed category SCones

| Paper | English statement | Rocq |
|---|---|---|
| Lem 7.1 | The gauge $N$ is a norm on the local cone $P=B_x$, and $P$ is a cone whose $0$, operations and order are those of $\mathcal{M}B$. | `local_cone` (`isCone.Build`), `lc_normh`, `lc_normt` — `theories/stable/local_cone.v` |
| Lem 7.2 | For $u\in\mathcal{M}B_x\setminus\{0\}$: $x+\lVert u\rVert^{-1}u$ stays in the unit ball, and $x+\lambda u$ leaves it for $\lambda>\lVert u\rVert^{-1}$. | `gauge_sup_reach`, `gauge_sup_gt_out` — `theories/stable/local_cone.v` |
| Lem 7.4 | The reindexing $\mathrm{in}_j$ is a parity-preserving bijection between $\mathcal{P}^{\epsilon}(n)$ and $\{J\in\mathcal{P}^{\epsilon}(n+1)\mid j\in J\}$. | `Ppos_split_in`, `Pneg_split_in`, `Ppos_split_out`, `Pneg_split_out` — `theories/stable/findiff.v` |
| Def 7.5 | A function $f:\mathcal{B}P\to Q$ is *totally monotonic* if its iterated finite differences over the parity lattice satisfy $\sum_{I\in\mathcal{P}^-(n)}f(x+\sum_{i\in I}u_i)\le\sum_{I\in\mathcal{P}^+(n)}f(x+\sum_{i\in I}u_i)$. | `is_totmono`, `Pneg`/`Ppos` — `theories/stable/totmono.v` |
| Def 7.7 | A function is *stable* if it is totally monotonic, bounded, and $\omega$-continuous on the unit ball. | `is_stable` (uses `is_scott_continuous_unit`) — `theories/stable/totmono.v` |
| Def 7.10 | A *measurable stable* function additionally sends measurable paths $X\to C$ to measurable paths $X\to D$. | `is_meas_stable` — `theories/stable/totmono.v` |
| Lem 7.11 | The stable and measurable functions $C\to D$ form a precone under pointwise operations (closed under $0$, addition, and non-negative scaling). | `stable_zero`, `stable_add`, `stable_scale` — `theories/stable/totmono.v` |
| Lem 7.12 | The stable (cone) order coincides with the alternating finite-difference inequality: $f\le g$ iff a sign-split difference test holds. | `sh_le_of_alt` — `theories/stable/stablehom.v` |
| Def 7.15 | $f$ is *$n$-increasing* if it is increasing and each single-step difference $\Delta f(u)$ over the local cone $B_u$ is $(n-1)$-increasing. | `is_n_increasing` (Fixpoint on $n$) — `theories/stable/findiff.v` |
| Lem 7.16 | If $f$ is $n$-increasing for all $n$, then so is each single-step difference $\Delta f(u):\mathcal{B}\mathcal{M}B_u\to\mathcal{M}C$. | `is_n_increasing_Delta` — `theories/stable/findiff.v` |
| Lem 7.18 | If $f$ is totally monotonic, then so is each single-step difference $\Delta f(u):\mathcal{B}\mathcal{M}B_u\to\mathcal{M}C$. | `totmono_Delta1` — `theories/stable/findiff.v` |
| Thm 7.19 | $f$ is totally monotonic iff it is *$n$-increasing* for every $n\in\mathbb{N}$. | `totmono_is_n_increasing` (forward), `is_n_increasing_totmono` (converse) — `theories/stable/findiff.v` |
| Lem 7.20–7.25 | The finite-difference / sign-split machinery $\Delta^{\epsilon}$, $\Delta$, $\mathsf{S}^n B$ used to prove Thm 7.19 and the §7.3 closure properties. | `totmono_Delta_pos`/`_neg`, `SD`, `SD_cons`, `SnB`, `SnB_increasing`, etc. — `theories/stable/findiff.v` + `theories/stable/compose.v` |
| Lem 7.21 | For totally monotonic $f$, the iterated difference is bounded above by $f$ at the summed point: $\Delta f(\overrightarrow{u})(x)\le f(x+\sum_i u_i)$. | `Delta_le`, `SD_le` — `theories/stable/findiff.v` |
| Lem 7.26 | Faà-di-Bruno composition: $k(x)=\Delta g(h_1 x,\dots,h_n x)(f x)$ is totally monotonic when $g,f,h_i$ are and $f+\sum_i h_i$ stays in the unit ball. | `ninc_kfun`, `totmono_comp` — `theories/stable/compose.v` |
| Lem 7.27 | If $f$ is linear in its first argument and totally monotonic in its second, it is totally monotonic on the product of unit balls. | `ev_totmono` (delivered in the form actually needed by the CCC) — `theories/stable/scones_ccc.v` |
| Thm 7.30 | Stable (and measurable) functions of norm $\le 1$ are closed under composition. | `stable_comp`, `meas_stable_comp` — `theories/stable/compose.v` |
| Lem 7.31 | $\mathbf{ICones}(B,C)\subseteq\mathbf{SCones}(B,C)$: every linear morphism is stable, giving the forgetful functor $\mathsf{Der}$. | `linear_totmono`, `linear_stable`, `ders` — `theories/stable/scones_cat.v` |
| Thm 7.32 | The category $\mathbf{SCones}$ of stable functions has all products and is cartesian closed. | `SCones_ccc`, `SCones_CCC` (record + witness) — `theories/stable/scones_ccc.v` |
| Thm 7.34 | The forgetful functor $\mathsf{Der}:\mathbf{ICones}\to\mathbf{SCones}$ preserves all limits. | `der_preserves_prod_proj`, `der_preserves_limits` — `theories/stable/der_continuous.v` |
| (also) | Stable functions admit a least fixpoint via the cone unit-ball $\omega$-cpo (paper §9.2). | `lfp_fixpoint`, `sfix_fixpoint`, `Yfix`, `Yfix_fix` — `theories/stable/fixpoint.v` |

The `is_stable` predicate uses `is_scott_continuous_unit` (unit-ball input,
any-radius output sup) because the strictly-linear `is_omega_continuous`
(both $\omega$-chains in the unit ball) is **not preserved under non-negative
scaling for non-linear maps** — a faithful reading of the paper's setting,
not a weakening.

### Lem 7.1 (`local_cone`, `lc_normh`, `lc_normt`)

The local cone $B_x$ of $B$ at $x\in\mathcal{B}\mathcal{M}B$ is the set of directions $u$ with $x+\lambda u\in\mathcal{B}\mathcal{M}B$ for some $\lambda>0$; equipped with the gauge norm $N(u)=(\sup\{\lambda>0\mid x+\lambda u\in\mathcal{B}\mathcal{M}B\})^{-1}$ it is a cone whose $0$, algebraic operations and order are inherited from $\mathcal{M}B$. The algebraic half is the `isPrecone` instance, the norm laws are `lc_normh` (homogeneity) and `lc_normt` (sub-additivity), and the whole is assembled into the `isCone` HB instance on `local_cone x`.

> **Paper — Lemma 7.1** (arXiv 2212.02371, `lemma:local-cone-is-a-subcone`). The function $N$ is a norm on $P$ and, equipped with this norm, $P$ is a cone whose $0$ element and algebraic operations are those of $\mathcal{M}B$.

```coq
(* theories/stable/local_cone.v — Variables: R : realType, B : coneType R, x : B *)
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

(* Paper Lemma 7.1: B_x is a cone, norm the gauge lc_norm. *)
HB.instance Definition _ := @isCone.Build R (local_cone x)
  lc_norm
  lc_normh
  (fun (u : P) (H : lc_norm u = 0) => @lc_eq R B x u (lc_zero Hx) (lc_normz H))
  lc_normt
  (* (Normp) + (Normc) via lc_normp / lc_sup_ball, transported through lc_leE *)
  _ _ _ _ _.
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

```coq
(* theories/stable/findiff.v — Section Lemma718: R, B C, f, u, Hsu : ‖su‖ < 1, Bu := lc_coneType Hsu, oneu := fun _ : 'I_1 => u *)
Lemma totmono_Delta1 (Hf : is_totmono f) : @is_totmono R Bu C (Delta f oneu).
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

```coq
(* theories/stable/compose.v — Section vars: R, B C D, g : C -> D, Hg : is_totmono g *)
Definition kfun (n : nat) (f : B -> C) (h : 'I_n -> (B -> C)) : B -> D :=
  fun x => SD g (fun i => h i x) (f x).

Lemma ninc_kfun (p : nat) :
  forall (B : coneType R) (n : nat) (f : B -> C) (h : 'I_n -> (B -> C)),
  is_totmono f -> (forall i, is_totmono (h i)) ->
  (forall y : B, cone_norm y <= 1 ->
     cone_norm (f y + \big[precone_add/precone_zero]_(i : 'I_n) h i y) <= 1) ->
  is_n_increasing p (kfun g f h).

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

### Lem 7.31 (`linear_totmono`, `linear_stable`, `ders`)

Every linear (integrable-cone) morphism is stable, so the integrable-cone morphisms embed into the stable/measurable ones — this is the forgetful (dereliction) functor $\mathsf{Der}:\mathbf{ICones}\to\mathbf{SCones}$, acting as the identity on objects and morphisms. The core is `linear_totmono` (linearity implies total monotonicity), packaged with boundedness and $\omega$-continuity into `linear_stable`, and realized as the inclusion map `ders` on `icones_hom` (the underlying linear function $0$-extended off the unit ball).

> **Paper — Lemma 7.31** (arXiv 2212.02371). $\mathbf{ICones}(B,C)\subseteq\mathbf{SCones}(B,C)$.

```coq
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
| Lem 9.2 | Two linear maps ${!B_1}\otimes\cdots\otimes{!B_n}\to C$ agreeing on every promoted pure tensor $x_1^!\otimes\cdots\otimes x_n^!$ (for $x_i\in\mathcal{B}\underline{B_i}$) are equal. | `tens_excl_charact` (the $n=2$ case characterising the binary Seely iso), with `tens_excl_charact3` / `tens_excl_charact3l` the $n=3$ coherence instances — `theories/homs/seely.v` |
| Lem 9.3 | The exponential functor on a promoted point: $({!f})(x^!)=f(x)^!$. | `bang_fmap_prom` (the computation behind `bang_fmap_id` / `bang_fmap_comp` functoriality and `Coalg_coassoc`) — `theories/homs/bang.v` |
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

### Lem 9.2 (`tens_excl_charact`)

Promoted pure tensors are *jointly separating* for linear maps out of a tensor of exponentials: two maps $f,g\in\mathbf{ICones}({!B_1}\otimes\cdots\otimes{!B_n},C)$ that agree on every $x_1^!\otimes\cdots\otimes x_n^!$ (with each $x_i$ in the unit ball) are equal. This is what pins down the Seely isos: an equation on promoted pure tensors fully characterises a map. The formalization provides the $n=2$ case `tens_excl_charact` (used for the binary Seely iso $\mathsf{m}^2$) together with the two $n=3$ instances `tens_excl_charact3` (right-associated $!A\otimes(!B\otimes!C)$) and `tens_excl_charact3l` (left-associated $(!A\otimes!B)\otimes!C$) needed by the monoidal-coherence proofs.

> **Paper — Lemma 9.2** (arXiv 2212.02371, `lemma:tens-excl-equal-charact`). Let $n\geq 1$, let $B_1,\dots,B_n,C$ be objects of $\mathbf{ICones}$ and $f$ and $g$ be elements of $\mathbf{ICones}({!B_1}\otimes\cdots\otimes{!B_n},C)$ such that $f(x_1^!\otimes\cdots\otimes x_n^!)=g(x_1^!\otimes\cdots\otimes x_n^!)$ for all $(x_i\in\mathcal{B}\underline{B_i})_{i=1}^n$. Then $f=g$.

> **Difference.** The paper states the lemma for general $n$ (by induction). The mechanisation instantiates the $n=2$ case actually used to characterise the binary Seely iso, and the two $n=3$ cases (right- and left-associated) needed by the monoidal-functor associativity coherence; the $n=3$ proofs are the paper's induction step unfolded once, reducing to the $n=2$ case.

```coq
(* theories/homs/seely.v *)

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

### Lem 9.3 (`bang_fmap_prom`)

The exponential functor $!$ commutes with promotion on unit-ball points: for a linear map $f\in\mathbf{ICones}(B,C)$ and $x\in\mathcal{B}\underline{B}$, we have $({!f})(x^!)=f(x)^!$. This single computation is the engine behind functoriality of $!$ (`bang_fmap_id`, `bang_fmap_comp`), the naturality squares `der_nat` / `dig_nat`, the Seely naturality `Seely2_natural`, and the coalgebra coassociativity `Coalg_coassoc`.

> **Paper — Lemma 9.3** (arXiv 2212.02371, `lemma:excl-fun-prom`). Let $f\in\mathbf{ICones}(B,C)$ and $x\in\mathcal{B}\underline{B}$. We have $({!f})(x^!)=f(x)^!$.

```coq
(* theories/homs/bang.v *)

Lemma bang_fmap_prom (B C : ICone.type Ar) (f : icones_hom Ar B C) (x : B) :
  cone_norm x <= 1 -> Lfun (bang_fmap f) x! = prom (Lfun f x).
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
| SAFT engine | Freyd's special adjoint functor theorem, mechanised concretely: a complete, well-powered, locally small category with a small coseparator has a left adjoint to every continuous functor, built as a wide intersection of subobjects of a power of the coseparator. | `SubobjClassifier`, `wi_obj`, `wi_med`, `is_icones_left_adjoint` — `theories/icones/representable.v` |
| Tensor as SAFT left adjoint | $-\otimes C$ is constructed as the SAFT left adjoint of $(C\multimap -)$, using the concrete SAFT engine, so the tree carries no `Parameter`/`Axiom`. | `tensor`, `tensor_incl` — `theories/homs/tensor_construct.v` |
| Exponential as SAFT left adjoint | $\;! = E$ is constructed as the SAFT left adjoint of $\mathsf{Der}$, again via the concrete SAFT engine. | `Bang`, `Bang_incl`, `nl`, `lin` — `theories/homs/bang_construct.v` |
| Melliès Prop 26 | Every $!$-coalgebra $(A,h_A)$ is a retract of its cofree coalgebra $(!A,\delta_A)$ in $\mathrm{EM}(!)$. | `diagram81` — `theories/homs/em_cartesian.v` |
| Melliès Prop 20 | Retraction lifting: if $i$ is a coalgebra morphism with carrier retraction $r\circ i = \mathrm{id}$ and $i\circ f$ is a coalgebra morphism, then $f$ is a coalgebra morphism. | `coalg_mor_lift` — `theories/homs/em_cartesian.v` |
| Melliès Prop 27 | A retract of a commutative comonoid lifts to a commutative comonoid; the four transported comonoid laws. | `transp_counitL`, `transp_counitR`, `transp_cocomm`, `transp_coassoc` — `theories/homs/em_cartesian.v` |
| Melliès Prop 28 | The monoidal structure of a linear category is cartesian in $\mathrm{EM}(!)$; the comonoid predicate holds on **every** coalgebra. | `EMComon_all` — `theories/homs/em_cartesian.v` |
| Melliès Cor 17 | A symmetric monoidal category in which every object carries a monoidal-natural comonoid is cartesian, with product the tensor and terminal object the unit. | `ICones_EM_cartesian`, `EM_Cartesian` — `theories/homs/em_cartesian.v` |
| Fox η-law cofree | The cartesian η-law $\langle\pi_1,\pi_2\rangle = \mathrm{id}$ on cofree coalgebra pairs. | `em_pair_mor_proj_id_cofree` — `theories/programs/infra/cbv_adjunction.v` |
| Fox η-law general | The cartesian η-law $\langle\pi_1,\pi_2\rangle = \mathrm{id}$ for the $\mathrm{EM}(!)$ binary product on **every** pair of coalgebras. | `em_pair_mor_proj_id` — `theories/programs/infra/cbv_adjunction.v` |
| Melliès Prop 29 | The cofree-coalgebra adjunction $U\dashv\tilde{!} : \mathbf{ICones}\rightleftarrows\mathrm{EM}(!)$ is a linear/non-linear (lax symmetric monoidal) adjunction. | `CBV_Model`, `ICones_CBV` — `theories/programs/infra/cbv_adjunction.v` |

### SAFT engine (`SubobjClassifier`, `wi_obj`, `wi_med`, `is_icones_left_adjoint`)

The paper builds $\otimes$, $!$, and the Seely isos via Freyd's Special Adjoint Functor Theorem (SAFT), invoked as a black box. Rather than postulate it, we mechanise the SAFT argument concretely: the left adjoint of a continuous functor $F$ at $c$ is the *wide intersection* of the subobjects of a power of the coseparator $1$ over which $c\to F-$ factors. The engine is a subobject classifier (well-poweredness), binary and wide intersections of subobjects with their universal properties, an initiality argument, and the hom-bijection export contract a left-adjoint candidate must satisfy.

> **Source — Riehl, *Category Theory in Context*, Theorem 4.6.10 (Special Adjoint Functor Theorem)** (Dover/Cambridge, 2016; Theorem 4.7.10 in the online edition). Let $U : A \to S$ be a continuous functor whose domain is complete and whose domain and codomain are locally small. Furthermore, if $A$ has a small coseparating set and every collection of subobjects of a fixed object in $A$ admits an intersection, then $U$ admits a left adjoint.

> **Source — Riehl, *ibid.*, Lemma 4.6.11** (Lemma 4.7.11 online). Suppose $C$ is locally small, complete, has a small coseparating set $\Phi$, and has the property that every collection of subobjects has an intersection. Then $C$ has an initial object. (Proof: form the product $p = \prod_{k\in\Phi} k$ and the intersection $i \hookrightarrow p$ of all subobjects of $p$; then $i$ is initial.)

> **Source — Riehl, *ibid.*, Corollary 4.6.14** (Corollary 4.7.14 online). Suppose $C$ is locally small, complete, has a small coseparating set, and has the property that every collection of subobjects of a fixed object has an intersection. Then any continuous functor $F : C \to \mathbf{Set}$ is representable.

> **Difference.** SAFT is a *meta-theorem* about the existence of an adjoint; the mechanisation replaces the abstract statement with the concrete construction its proof supplies. `SubobjClassifier` / `icones_well_powered` discharge well-poweredness (Riehl's "each object admits only a set's worth of subobjects"); `pb_med` and `wi_obj`/`wi_med` build the binary and wide intersections of Lemma 4.6.11; and `is_icones_left_adjoint` records the hom-bijection contract a candidate left adjoint must satisfy. The coseparator is the unit cone $1$ (paper Thm 4.18), not the interval $I$ of Riehl's Stone–Čech example.

```coq
(* theories/icones/representable.v *)
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

### Exponential as SAFT left adjoint (`Bang`, `Bang_incl`, `nl`, `lin`)

The exponential $! = E$ is discharged as the SAFT left adjoint of the dereliction functor $\mathsf{Der}$: the object $\mathrm{Bang}\,B = E\,B$ is the wide intersection of the factoring subobjects of $B\multimap 1^{\mathbf{Ar}}$, with the universal nonlinear map `nl` and the linear factoriser `lin`.

> **Source — Riehl, *Category Theory in Context*, Theorem 4.6.10** (as above). A continuous functor out of a complete, locally small, well-powered category with a small coseparator admits a left adjoint, given concretely by the wide intersection of the factoring subobjects of a power of the coseparator.

> **Difference.** The paper's §7 (Thm 7.34) supplies the limit-preservation of $\mathsf{Der}$ and then invokes SAFT for $!$; the mechanisation runs the concrete engine, so `Bang`, `nl`, `lin` are proved definitions with no axiom interface. Continuity of $\mathsf{Der}$ (Thm 7.34) is in `theories/stable/der_continuous.v`.

```coq
(* theories/homs/bang_construct.v *)
Module Icones_bang_construct.
Definition Bang : ICone.type Ar := wi_obj fhh fk0.
Definition Bang_incl : icones_hom Ar Bang p := wi_incl fAdom fhh fk0.
Definition nl  : scones_hom B (Bang B) := (* the universal nonlinear map *) _.
Definition lin : icones_hom Ar (Bang B) C := (* the linear factoriser *) _.
End Icones_bang_construct.
```

### Melliès Prop 26 (`diagram81`)

Every $!$-coalgebra $(A,h_A)$ is a retract of its cofree coalgebra $(!A,\delta_A)$, via $A\xrightarrow{h_A}!A\xrightarrow{\varepsilon_A}A$. The formalisation records the key retraction square (Melliès' Eq (81)/(88)) as `diagram81`.

> **Source — Melliès, *Categorical Semantics of Linear Logic* (Panoramas et Synthèses 27, SMF 2009), Proposition 26.** In a linear category $L$, every coalgebra $(A, h_A)$ induces a retraction $A\xrightarrow{h_A}!A\xrightarrow{\varepsilon_A}A$ making the diagram $$\begin{array}{ccc} A & \xrightarrow{\;h_A\;} & !A\\[2pt] {\scriptstyle d_A}\downarrow & & \downarrow{\scriptstyle d_A}\\[2pt] A\otimes A & \xrightarrow{\;h_A\otimes h_A\;} & !A\otimes\,!A \end{array}$$ commute (with $\varepsilon_A\otimes\varepsilon_A$ the retraction of $h_A\otimes h_A$).

> **Difference.** Melliès states the square in a generic linear category; the mechanisation instantiates it at the icones comonad $!$ and records the concrete morphism equality `diagram81` (the transported diagonal via the structure map `coalg_str`), which the Cor-20 lift then consumes.

```coq
(* theories/homs/em_cartesian.v *)
Lemma diagram81 (P : Coalgebra Ar) :
  icones_comp (tensor_mor (coalg_str P) (coalg_str P)) (coalg_d P) =
  icones_comp (d_bang (coalg_obj P)) (coalg_str P).
```

### Melliès Prop 20 (`coalg_mor_lift`)

The retraction-lifting property Melliès flags as *"less obvious"*: given a carrier retraction $r\circ i = \mathrm{id}$ with $i$ a coalgebra morphism, a map $f$ is a coalgebra morphism iff $i\circ f$ is. The formalisation mechanises the (66)/(67) diagram chase as `coalg_mor_lift`.

> **Source — Melliès, *ibid.*, §6.11 Proposition 20.** Suppose given a comonad $(K,\mu,\eta)$, two coalgebras $(A,h_A)$, $(B,h_B)$, and a retraction $A\xrightarrow{i}B\xrightarrow{r}A = \mathrm{id}_A$ between the underlying objects, with $i : (A,h_A)\to(B,h_B)$ a coalgebra morphism. Then, for every coalgebra $(X,h_X)$ and morphism $f : X\to A$, the following are equivalent: (i) $f$ is a coalgebra morphism $(X,h_X)\to(A,h_A)$; (ii) the composite $i\circ f$ is a coalgebra morphism $(X,h_X)\to(B,h_B)$.

> **Difference.** The REFERENCE MAP cites this as "Cor 20 / Prop 20"; in Melliès it is Proposition 20 of §6.11 (a lifting property of the coalgebra morphism $i$). The mechanisation gives the $(\Leftarrow)$ direction directly as `coalg_mor_lift` and applies it at the retraction $(h_A\otimes h_A)/(\varepsilon_A\otimes\varepsilon_A)$ to show the transported diagonal $d_A$ is a coalgebra morphism.

```coq
(* theories/homs/em_cartesian.v *)
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
(* theories/homs/em_cartesian.v *)
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
(* theories/homs/em_cartesian.v *)
Lemma EMComon_all (P : Coalgebra Ar) : EMComon P.
```

### Melliès Cor 17 (`ICones_EM_cartesian`, `EM_Cartesian`)

The bridge from comonoids to a cartesian structure: a symmetric monoidal category in which every object carries a monoidal-natural comonoid is cartesian, with product carried by the tensor and terminal object the unit. The headline `ICones_EM_cartesian` bundles the full cartesian structure of $\mathrm{EM}(!)$ (product, terminal, projections, pairing, β-laws, terminal UP), the product being the linear $\otimes$.

> **Source — Melliès, *ibid.*, Corollary 17.** Let $(C,\otimes,1)$ be a symmetric monoidal category. The tensor product is a cartesian product and the tensor unit is a terminal object if and only if there exists a pair of monoidal natural transformations $d$ and $e$ with components $d_A : A\to A\otimes A$ and $e_A : A\to 1$ defining a comonoid $(A, d_A, e_A)$ for every object $A$.

> **Difference.** Melliès' Corollary 17 does *not* require the comonoids to be commutative; the underlying classical result is Fox's theorem (T. Fox, *Coalgebras and cartesian categories*, Comm. Algebra 4, 1976). The mechanisation records the cartesian package as the record `EM_Cartesian` and populates every field in `ICones_EM_cartesian`, with the binary product carried by the linear tensor $\otimes$ — not the cartesian $\&$.

```coq
(* theories/homs/em_cartesian.v *)
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

### Fox η-law cofree (`em_pair_mor_proj_id_cofree`)

The cartesian η-law $\langle\pi_1,\pi_2\rangle = \mathrm{id}$ on the cofree pair $(\tilde{!}A, \tilde{!}B)$: it reduces, via `tens_excl_charact`, to a computation on the promoted tensor $x^{!}\otimes y^{!}$. This is genuinely additional content beyond the β-laws.

> **Source — Fox, *Coalgebras and cartesian categories*, Comm. Algebra 4(7):665–667, 1976 (Fox's theorem).** *(Faithful paraphrase.)* A symmetric monoidal category is cartesian iff every object carries a (uniform, natural) cocommutative comonoid structure for which every morphism is a comonoid homomorphism; equivalently the category of cocommutative comonoids is the cartesian coreflection, with the tensor of comonoids serving as their categorical product. In particular the product's η-law $\langle\pi_1,\pi_2\rangle = \mathrm{id}$ holds, uniquely determined by the comonoid structure.

> **Difference.** The β-laws only give the universal property *out of* a coalgebra; the η-law is Fox's theorem specialised to $\mathrm{EM}(!)$ of a linear-exponential comonad (Melliès Prop 28 at the icones level). The cofree case `em_pair_mor_proj_id_cofree` establishes η on promoted tensors by Melliès' retract-and-lift technique, *not* by promoted-point reduction.

```coq
(* theories/programs/infra/cbv_adjunction.v *)
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
(* theories/programs/infra/cbv_adjunction.v *)
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
(* theories/programs/infra/cbv_adjunction.v *)
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
   logic core: $(\mathbf{ICones}, \otimes, \mathbf{1})$ is a SMCC.
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
