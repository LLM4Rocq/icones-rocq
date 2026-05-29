# AUDITOR.md — paper-to-Rocq correspondence

This document is for a **paper reviewer / mathematician** auditing the Icones
formalisation. It maps each definition / lemma / theorem of the paper to its
Rocq counterpart, so you can verify *what is formalised* without having to read
the proof scripts themselves. Notable mathematical content we had to add to
make the paper machine-checkable (SAFT mechanisation, the Cor-20 retraction-
and-lifting, the LNL/Seely structure, the CBV calculi) is in a separate section.

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
| Def 2.1 | A *precone* is an additive commutative monoid with a non-negative real scalar action satisfying distributivity and bilinearity. | `precone`, `PreCone.type` — `theories/cones/precone.v` |
| Def 2.2 | A *cone* is a precone with a partial order ≤ (Selinger's), the supremum of every increasing norm-bounded ω-chain, and the norm acting as a continuous semi-norm. | `Cone.type` — `theories/cones/cone.v` |
| Cat 2 | The category **Cones** has cones as objects and norm-≤ 1 continuous linear maps as morphisms. | `cones_hom`, `cones_comp`, `Cones` (the category) — `theories/cones/cone_cat.v` |
| Lem 2.8 / 2.10 | ω-continuity of inverse / of the difference operator on the unit ball. | `invf_omega_continuous`, `diff_omega_continuous` — `theories/cones/basic_lemmas.v` |

Notable design choice: ω-continuity comes in two flavours — `is_omega_continuous`
(input and output chains live in the unit ball; linear-tailored) and
`is_scott_continuous_unit` (input chain in the ball, output at any radius;
the *general* notion needed for non-linear stable maps in §7). Both are
proved equivalent for linear maps.

### Def 2.1 (`isPrecone` / `Precone`)

```coq
(* theories/cones/precone.v *)
HB.mixin Record isPrecone (R : realType) (P : Type) := {
  precone_zero  : P;
  precone_add   : P -> P -> P;
  precone_scale : {nonneg R} -> P -> P;
  (* Algebraic axioms — Paper §2.1 (R≥0-semimodule structure) *)
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
  (* (Cancel) — Paper §2.1 *)
  precone_cancel :
    forall x y z, precone_add x y = precone_add x z -> y = z;
  (* (Pos) — Paper §2.1 *)
  precone_pos :
    forall x y, precone_add x y = precone_zero ->
                x = precone_zero /\ y = precone_zero;
}.

#[short(type="preconeType")]
HB.structure Definition Precone (R : realType) := { P of isPrecone R P }.
```

### Def 2.2 (`isCone` / `Cone`)

```coq
(* theories/cones/cone.v *)
HB.mixin Record isCone (R : realType) P of Precone R P := {
  cone_norm : P -> R;
  (* (Normh) ‖λ·x‖ = λ·‖x‖ *)
  cone_normh : forall (r : {nonneg R}) (x : P),
    cone_norm (precone_scale r x) = r%:num * cone_norm x;
  (* (Normz) ‖x‖ = 0 ⇒ x = 0 *)
  cone_normz : forall x : P, cone_norm x = 0 -> x = precone_zero;
  (* (Normt) sub-additivity *)
  cone_normt : forall x y : P,
    cone_norm (precone_add x y) <= cone_norm x + cone_norm y;
  (* (Normp) order-monotonicity *)
  cone_normp : forall x y : P,
    precone_le x y -> cone_norm x <= cone_norm y;
  (* (Normc) ω-completeness of the unit ball, packaged as an operator *)
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

```coq
(* theories/cones/cone_cat.v — Section ConesHom, Variables R Q P *)

(** Paper Definition 2.17: a morphism in [Cones]. *)
Record cones_hom (P Q : coneType R) : Type := ConesHom {
  cones_hom_fun :> P -> Q;
  cones_hom_linear : is_linear cones_hom_fun;
  cones_hom_continuous : is_omega_continuous cones_hom_fun;
  cones_hom_norm_le1 :
    forall x : P, cone_norm (cones_hom_fun x) <= cone_norm x;
}.

(** Paper Definition 2.17: composition in [Cones]. *)
Definition cones_comp (g : cones_hom Q S) (f : cones_hom P Q) :
  cones_hom P S.
Proof. (* refine (ConesHom (g \o f) ...) ; proof omitted *) Defined.
```

The category `Cones` is the locally-small category whose hom-type is
`cones_hom` and whose composition is `cones_comp`; it is not packaged as a
named record here (the project follows PLAN Strategy C: no abstract
`Category` typeclass).

### Lem 2.8 / 2.10 (`invf_omega_continuous`, `diff_omega_continuous`)

```coq
(* theories/cones/basic_lemmas.v *)
(* Section variables: R : realType, P Q : coneType R,
   f : P -> Q linear, ω-continuous, injective, surjective ;
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
| `ARCAT` | A small full subcategory of `MEAS` whose objects have a 1-element and whose binary products live in the subcategory. | `MeasSubcat`, `ar_obj`, `ar_carrier`, `ar_point`, `ar_zero`, `ar_prod` — `theories/mcones/ar.v` |
| Def 3.5 | A *measurable cone* is a cone equipped with a family of measurable tests (continuous, ≤ 1, separating). | `MCone.type` (via `isMCone` mixin) — `theories/mcones/mcone.v` |
| Def 3.13 | An *mcones morphism* is a `Cones`-morphism preserving the test family. | `mcones_hom`, `mcones_comp`, `MCones` — `theories/mcones/mcone_cat.v` |
| Prop 3.11 | Dual norm separation: `‖x‖ ≤ sup_{t∈Mtest} ⟨t,x⟩`, with the supremum attained as an adherent point. | `mcone_norm_le_pairing_ub`, `mcone_test_pairing_adherent` — `theories/mcones/mcone_cat.v` (`Section Proposition311`) |
| Def 3.16 | The *measure cone* `FMeas(X)` of finite measures on `X ∈ ARCAT`, with test `t ↦ ∫ t dµ`. | `fmeas`, the `FMeas` HB instance — `theories/mcones/fmeas.v` |
| Def 3.20 | A *path* is a measurable map `r ↦ η(r) : X → C` whose pointwise test pairings are measurable. | `path_car` — `theories/mcones/path.v`; `path_int_exists` lives in `theories/icones/examples_icone.v` (see § 4 below) |
| Cat 3 | `MCones` is a category. | `MCones` (above) — `theories/mcones/mcone_cat.v` |

The Rocq encoding faithfully treats `ARCAT` as a parameter (`MeasSubcat R`)
just as the paper does (paper §3, around `content.tex:1029`).

> **Path note.** The original table cited `path_int_exists` as living in
> `theories/mcones/path.v`, but it is in fact stated as the
> `isICone`-witness `path_int_exists` in `theories/icones/examples_icone.v`
> (path is integrable iff its codomain is — paper Thm 4.12). Fixed in
> this revision; the underlying path data type `path_car` does live in
> `path.v`.

### `ARCAT` (`MeasSubcat`)

```coq
(* theories/mcones/ar.v *)
Record MeasSubcat (R : realType) : Type := MkMeasSubcat {
  ar_obj     : Type;
  ar_disp    : ar_obj -> measure_display;
  ar_carrier : forall X : ar_obj, measurableType (ar_disp X);
  (* Paper §3: all objects of [Ar] are non-empty. *)
  ar_point   : forall X : ar_obj, ar_carrier X;
  (* Paper §3: [Ar] contains the terminal object [0]. *)
  ar_zero    : ar_obj;
  ar_zero_singleton :
    forall x y : ar_carrier ar_zero, x = y;
  (* Paper §3: [Ar] is closed under cartesian products,
     and the carrier of the product is *definitionally* the
     [measurableType] product. *)
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

### Def 3.5 (`isMCone` / `MCone`)

```coq
(* theories/mcones/mcone.v *)
HB.mixin Record isMCone (R : realType) (Ar : MeasSubcat R) C of Cone R C := {
  (** Paper Def 3.2: the family [M = (M_X)_{X ∈ Ar}]. *)
  mcone_M : forall X : ar_obj Ar, set (test_of Ar X C);
  (** (Mscomp): closure under reindexing by [ar_hom]. *)
  mcone_M_comp :
    forall (Y X : ar_obj Ar) (φ : ar_hom Ar Y X) (m : test_of Ar X C),
      mcone_M X m -> mcone_M Y (test_reindex φ m);
  (** (Mssep): tests at arity 0 separate points. *)
  mcone_M_sep :
    forall x1 x2 : C,
      (forall m : test_of Ar (ar_zero Ar) C,
        mcone_M (ar_zero Ar) m ->
        test_fun m (ar_zero_pt Ar) x1 = test_fun m (ar_zero_pt Ar) x2) ->
      x1 = x2;
  (** (Msnorm) Remark 3.3 form: norm is ε-approximated by a test pairing. *)
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

```coq
(* theories/mcones/mcone_cat.v — Section Proposition311,
   Variables (R : realType) (Ar : MeasSubcat R) (B : MCone.type Ar) *)

(** Paper Prop 3.11 (≤ direction): for non-zero [x] and ε > 0,
    there is a pairing within ε of [‖x‖]. *)
Lemma mcone_test_pairing_adherent (x : B) (eps : R) :
  x <> precone_zero -> 0 < eps ->
  exists2 y, mcone_test_pairing_set x y & cone_norm x <= y + eps.

(** Paper Prop 3.11: any [M] upper-bounding the pairing set
    dominates [‖x‖]. *)
Lemma mcone_norm_le_pairing_ub (x : B) (M : R) :
  x <> precone_zero ->
  ubound (mcone_test_pairing_set x) M -> cone_norm x <= M.
```

### Def 3.16 (`fmeas`, `FMeas`)

```coq
(* theories/mcones/fmeas.v — Variables R X *)
Record fmeas : Type := MkFmeas {
  fmeas_mu        :> {measure set X -> \bar R};
  fmeas_fin       : fmeas_finP fmeas_mu;
  fmeas_canonical : fmeas_canon fmeas_mu;
}.

(** Paper §3.2.1: register the [isMCone] instance on [fmeas R X]. *)
HB.instance Definition _ :=
  @isMCone.Build R Ar (fmeas R X)
    fmeas_mcone_M
    fmeas_mcone_M_comp
    fmeas_mcone_M_sep
    fmeas_mcone_M_norm.
```

### Def 3.20 (`path_car`)

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
| Def 4.2 | The Pettis integral `∫_µ η : C` is the unique element pairing with every test `t` as `∫ ⟨t, η(r)⟩ dµ`. | `icone_integral`, `icone_integral_eqP` (uniqueness) — `theories/icones/icone.v` |
| Lem 4.7 | The Pettis integral satisfies the natural change-of-variable / Fubini-type identities (the conversion lemma threading all integrability arguments). | `icone_integral_*` family + `bilin.v` — `theories/icones/pettis.v`, `theories/homs/bilin.v` |
| Thm 4.5 | The set of paths into a cone is itself an `ICone`. | `path_isICone` (via `path_int_exists`) — `theories/mcones/path.v`, `theories/icones/examples_icone.v` |
| Thm 4.12 | `FMeas(X)` and the dual cone `⊥` are integrable. | `FMeas` is an `ICone`; `Bottom`-cone instances — `theories/icones/examples_icone.v` |
| Cat 4 | The category `ICones` has integrable cones and `MCones`-morphisms preserving the integral. | `icones_hom`, `icones_comp`, `ICones` — `theories/icones/icone_cat.v` |
| Fubini (§4) | The Fubini / iterated-integral identity for paths over a product space. | `fubini_iter_fun_X` — `theories/icones/fubini.v` |
| Thm 4.18 | `ICones` is well-powered. | `icones_well_powered` (full proof, no stub) — `theories/icones/representable.v` |
| Thm 4.19 | `ICones` is complete with `1` a coseparator; therefore every limit-preserving functor `ICones → C` has a left adjoint (by SAFT). | The completeness data (products, equalisers, the coseparator) is in `icone_cat.v`; the bespoke **SAFT engine** is `representable.v` (`wi_obj`, `wi_med`, `is_icones_left_adjoint`) — see *Beyond the paper* below |

### Def 4.1 / 4.3 (`isICone`, `ICone`)

```coq
(* theories/icones/icone.v *)
HB.mixin Record isICone (R : realType) (Ar : MeasSubcat R) B
  of MCone R Ar B := {
  (** Paper Def 4.3: every measurable path admits a Pettis integral
      with respect to every finite measure. *)
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

### Def 4.2 (`icone_integral`, `icone_integral_eqP`)

```coq
(* theories/icones/icone.v — Section ICOneIntegral,
   Variables R Ar B X β Hβ µ *)

(** The value [I^B_X(β, µ)]. *)
Definition icone_integral : B :=
  path_integral (icone_exists X β Hβ µ).

(** Specification: it satisfies [path_integral_eq]. *)
Lemma icone_integralP : path_integral_eq β µ icone_integral.

(** Uniqueness: any candidate satisfying the defining equation
    equals [icone_integral]. *)
Lemma icone_integral_eqP (x : B) :
  path_integral_eq β µ x -> x = icone_integral.
```

### Lem 4.7 (`icone_integral_*` family + `bilin.v`)

```coq
(* theories/icones/icone_integral.v — Section variables R Ar B X β Hβ µ *)

(** Lemma 4.7: additivity in [β]. *)
Lemma icone_integral_addB
  (β1 β2 : ar_carrier Ar X -> B)
  (Hβ1 : is_measurable_path β1) (Hβ2 : is_measurable_path β2)
  (Hβ12 : is_measurable_path (fun r => precone_add (β1 r) (β2 r))) :
  icone_integral (fun r => precone_add (β1 r) (β2 r)) Hβ12 µ =
  precone_add (icone_integral β1 Hβ1 µ) (icone_integral β2 Hβ2 µ).

(** Lemma 4.7: scalar in [β]. *)
Lemma icone_integral_scaleB
  (r : {nonneg R}) (β : ar_carrier Ar X -> B)
  (Hβ : is_measurable_path β)
  (Hrβ : is_measurable_path (fun u => precone_scale r (β u))) :
  icone_integral (fun u => precone_scale r (β u)) Hrβ µ =
  precone_scale r (icone_integral β Hβ µ).

(** Lemma 4.7: additivity in [µ]. *)
Lemma icone_integral_addmu (µ1 µ2 : fmeas R (ar_carrier Ar X)) :
  icone_integral β Hβ (fmeas_add µ1 µ2) =
  precone_add (icone_integral β Hβ µ1) (icone_integral β Hβ µ2).

(** Lemma 4.7: scalar in [µ]. *)
Lemma icone_integral_scalemu
  (r : {nonneg R}) (µ : fmeas R (ar_carrier Ar X)) :
  icone_integral β Hβ (fmeas_scale r µ) =
  precone_scale r (icone_integral β Hβ µ).

(** Companions used as Lemma 4.7 instances downstream. *)
Lemma icone_integral_test_pettis (Z : ar_obj Ar) (* ... *).
Lemma icone_integral_chain_le : (* ... *).
Lemma icone_integral_joint_measurable : (* ... *).
```

### Thm 4.12 (`path_int_exists`, `FMeas`/`⊥` `isICone` instances)

```coq
(* theories/icones/examples_icone.v *)

(** Paper Thm 4.12 (full): unconditional path-integrability for
    [path_car Ar X B], given the cast-measurability hypotheses. *)
Lemma path_int_exists
    (Y' : ar_obj Ar)
    (η : ar_carrier Ar Y' -> P)
    (Hη : is_measurable_path η)
    (ν : fmeas R (ar_carrier Ar Y')) :
  is_path_integrable η ν.

(** Register the [isICone] instance on [path_car Ar X B]. *)
HB.instance Definition _ : isICone R Ar P :=
  isICone.Build R Ar P (@path_int_exists).

(** Paper §4: the [isICone] instance on [cone_one_car Ar] (= the unit). *)
HB.instance Definition _ :=
  @isICone.Build R Ar (cone_one_car Ar) (* ... witness ... *).

(** Paper Thm 4.5: the [isICone] instance on [fmeas R (ar_carrier Ar X)]. *)
HB.instance Definition _ :=
  @isICone.Build R Ar (fmeas R (ar_carrier Ar X)) (* ... witness ... *).
```

### Def 4.10 (`icones_hom`, `icones_comp`, `ICones`)

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

(** Identity in [ICones]. *)
Definition icones_id : icones_hom Ar B B :=
  MkIConesHom (mcones_id Ar B) icones_id_pres_int.

(** Composition in [ICones]. *)
Definition icones_comp
    (g : icones_hom Ar B C) (f : icones_hom Ar A B) : icones_hom Ar A C :=
  MkIConesHom
    (mcones_comp (icones_hom_mcones g) (icones_hom_mcones f))
    (icones_comp_pres_int g f).
```

### Fubini (`fubini_iter_fun_X`)

```coq
(* theories/icones/fubini.v — Variables
   R Ar B (X Y : ar_obj Ar)
   (β : ar_carrier Ar X * ar_carrier Ar Y -> B)
   (ν : fmeas R (ar_carrier Ar Y)) *)

(** The pointwise [x ↦ ∫_y β(x,y) dν] function. *)
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

```coq
(* theories/icones/representable.v — Section Classifier,
   Variables (R : realType) (Ar : MeasSubcat R), B : ICone.type Ar *)

(** The classifier type: a fixed small [Type], independent of the
    subobject's domain. *)
Record SubobjClassifier : Type := MkClassifier {
  cls_S    : set B;
  cls_add  : B -> B -> B;
  cls_scl  : {nonneg R} -> B -> B;
  cls_zer  : B;
  cls_nrm  : B -> R;
  cls_M    : forall X : ar_obj Ar,
               set (ar_carrier Ar X -> B -> R);
}.

(** Injectivity up to iso: subobjects with equal classifier are iso over [B]. *)
Lemma icones_subobject_classP (D1 D2 : icones_subobject B) :
  icones_subobject_class D1 = icones_subobject_class D2 ->
  subobject_equiv D1 D2.

(** Paper Thm 4.18 — the well-poweredness statement, the property SAFT consumes. *)
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
| Def 5.1 / 5.7 | The internal hom `C ⊸ D` carrier (the cone of `Cones`-morphisms `C → D`); its action `(h ⊸ g) : (C₁ ⊸ D₁) → (C₂ ⊸ D₂)`. | `linhom_car`, `linhom_postc`, `linhom_prec`, `linhom_map` — `theories/homs/linhom.v` |
| Prop 5.8 | The internal-hom action lifts to an `icones` morphism. | `linhom_map_icones` — `theories/homs/linhom_functor.v` |
| Thm 5.9 | The functor `(C ⊸ −)` preserves all limits. | `limpl_preserves_prod`, `limpl_preserves_limits` — `theories/homs/limpl_continuous.v` |
| Thm 5.12 | The currying isomorphism `(B ⊗ C) ⊸ D ≃ B ⊸ (C ⊸ D)`. | `tensor_hom_iso` — `theories/homs/tensor_iso.v` |
| Thm 5.13 | Norm identity: `‖m‖ = ‖curry m‖` for `m : B ⊗ C → D`. | `tensor_norm_le` (≤) + the ≥ direction via Prop 3.11 — `theories/homs/tensor.v` / `tensor_iso.v` |
| Prop 5.14 | The tensor is determined on pure tensors `x ⊗ y`. | `tensor_ext`, `tensor_ext3`, `tensor_ext4` — `theories/homs/tensor.v`, `theories/homs/smcc.v` |
| Thm 5.15 | `(ICones, ⊗, 1)` is a symmetric monoidal closed category. | `ICones_SMCC`, `ICones_smcc` — `theories/homs/smcc.v` |
| Rem 5.1 | The tensor object is given by SAFT, without an explicit carrier. | The paper's invocation of SAFT is *mechanised* concretely in `representable.v` + `tensor_construct.v` — see *Beyond the paper* below |

### Def 5.1 / 5.7 (`linhom_car`, `linhom_postc`, `linhom_prec`, `linhom_map_fun`)

```coq
(* theories/homs/linhom.v — Section LinhomCar,
   Variables (R : realType) (Ar : MeasSubcat R), C D : ICone.type Ar *)

(** Paper §5.1: the integrable-linear-map carrier — a [linhom_pre]
    (linear, ω-continuous, norm-bounded, path-preserving) plus
    integral-preservation. *)
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

```coq
(* theories/homs/linhom_functor.v *)
(** Paper Prop 5.8: the action of [⊸] on morphisms as an [icones_hom]. *)
Definition linhom_map_icones : icones_hom Ar (linhom_car Ar C1 D1)
                                            (linhom_car Ar C2 D2) :=
  MkIConesHom linhom_map_mcones linhom_map_pres_int.
```

### Thm 5.9 (`limpl_preserves_prod`, `limpl_preserves_limits`)

```coq
(* theories/homs/limpl_continuous.v *)

(** Paper Thm 5.9 (products): [⟨ C ⊸ π_i ⟩_i] is an iso, so [C ⊸ −]
    preserves the product [&_i D_i]. *)
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

(** Paper Thm 5.9 (packaged): [C ⊸ −] preserves products and
    equalisers, hence all limits. *)
Theorem limpl_preserves_limits : limpl_continuous.
```

### Thm 5.12 (`tensor_hom_iso`)

```coq
(* theories/homs/tensor.v — Section Tensor *)
Definition tensor_hom_Phi (B C D : ICone.type Ar) :
    icones_iso Ar ((B ⊗ C) ⊸ D) (B ⊸ (C ⊸ D)) :=
  tensor_hom_iso B C D.
```

### Thm 5.13 (`tensor_norm_le`, `tensor_normME`)

```coq
(* theories/homs/tensor.v *)

(** Thm 5.13 (≤ direction). *)
Lemma tensor_norm_le (B C : ICone.type Ar) (x : B) (y : C) :
  cone_norm (x ⊗p y) <= cone_norm x * cone_norm y.

(** Thm 5.13 (full equality). *)
Lemma tensor_normME (B C : ICone.type Ar) (x : B) (y : C) :
  cone_norm (x ⊗p y) = cone_norm x * cone_norm y.
```

### Prop 5.14 (`tensor_ext`, `tensor_ext3`, `tensor_ext4`)

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

(** Paper Thm 5.15: the canonical SMCC structure on [ICones]. *)
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
| Cat 6 | The category `Skern` of substochastic kernels: objects in `ARCAT`, morphisms `κ : X ⇝ FMeas(Y)`. | `Skern_hom`, `Skern_id`, `Skern_comp`, `Skern` — `theories/kernels/skern.v` |
| Thm 6.1 | Bijection `Path(X, B) ≃ FMeas(X) ⊸ B` (cone iso) given by the integration map `I^B_X`. | `int_to_linhom`, `int_to_linhom_iso` — `theories/homs/bilin.v` |
| Thm 6.5 | The functor `Klin : Skern → ICones`, sending `X ↦ FMeas(X)` and a kernel to its integration map, is **fully faithful**. | `Skern_to_ICones_fully_faithful` (= the *regression anchor*) — `theories/kernels/kernel_embedding.v` |

`Skern_to_ICones_fully_faithful` is the lemma checked by `./verify.sh` and is
load-bearing for the whole development's axiom budget. It depends only on the
3 classical `boolp` axioms.

### Cat 6 (`Skern_hom`, `Skern_id`, `Skern_comp`)

```coq
(* theories/kernels/skern.v — Section SkernHom, Variables R Ar *)

(** Paper §6.1: [Skern(X, Y) = B_{Path(X, FMeas(Y))}], i.e.
    measurable paths of unit-ball norm. *)
Record Skern_hom (X Y : ar_obj Ar) : Type := MkSkernHom {
  skern_path     : path_car Ar X (fmeas R (ar_carrier Ar Y));
  skern_norm_le1 : path_norm skern_path <= 1;
}.

(** Identity in [Skern] is the Dirac path. *)
Definition Skern_id : Skern_hom Ar X X :=
  MkSkernHom (dirac_path Ar X) dirac_path_norm_le1.

(** Kleisli composition: [(κ ∘ λ)(r) := int_to_linhom_fun κ (λ r)]. *)
Definition Skern_comp_path (λ : Skern_hom Ar X Y) (κ : Skern_hom Ar Y Z) :
    path_car Ar X (fmeas R (ar_carrier Ar Z)) :=
  MkPath (int_to_linhom_fun_pres_path (skern_path κ)
            (path_is_path (skern_path λ))).

Definition Skern_comp (λ : Skern_hom Ar X Y) (κ : Skern_hom Ar Y Z) :
    Skern_hom Ar X Z :=
  MkSkernHom (Skern_comp_path λ κ) (Skern_comp_norm_le1 λ κ).
```

### Thm 6.1 (`int_to_linhom`, `int_to_linhom_iso`)

```coq
(* theories/homs/bilin.v *)

(** The underlying function: [µ ↦ icone_integral β Hβ µ]. *)
Definition int_to_linhom_fun :
    fmeas R (ar_carrier Ar X) -> B :=
  fun µ => icone_integral βf Hβ µ.

(** Packaged as a [linhom_car]. *)
Definition int_to_linhom :
    linhom_car Ar (fmeas R (ar_carrier Ar X)) B :=
  MkLinhom int_to_linhom_pre
    (fun Y β' Hβ' µ' => int_to_linhom_fun_pres_int β Hβ' µ').

(** Paper Thm 6.1: [Path(X, B) ≃ FMeas(X) ⊸ B] as an iso in [Cones]. *)
Definition int_to_linhom_iso : cones_iso P L :=
  MkConesIso int_to_linhom_cones linhom_to_int_cones
    int_to_linhom_conesK int_to_linhom_conesK'.
```

### Thm 6.5 (`Skern_to_ICones_fully_faithful`)

```coq
(* theories/kernels/kernel_embedding.v *)

(** Paper Theorem 6.5 — the regression anchor. *)
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
| Def 7.5 | A function is *totally monotonic* if its iterated finite differences over the inclusion lattice are positive. | `is_totmono`, `Pneg`/`Ppos`, `\sumP` — `theories/stable/totmono.v` |
| Def 7.7 | A function is *stable* if it is totally monotonic, bounded, and ω-continuous on the unit ball. | `is_stable` (uses `is_scott_continuous_unit`) — `theories/stable/totmono.v` |
| Def 7.10 | A *measurable stable* function additionally preserves measurable paths. | `is_meas_stable` — `theories/stable/totmono.v` |
| Lem 7.11 | The class of stable functions is closed under zero, addition, and non-negative scaling. | `stable_zero`, `stable_add`, `stable_scale` — `theories/stable/totmono.v` |
| Lem 7.12 | Pointwise order on stable maps = the alternating-sum order. | `sh_le_of_alt` — `theories/stable/stablehom.v` |
| Thm 7.19 | A function is totally monotonic iff it is *n-increasing* (for all `n ≥ 1`). | `totmono_is_n_increasing` (forward), `is_n_increasing_totmono` (converse) — `theories/stable/findiff.v` |
| Lem 7.20–7.25 | The finite-difference / sign-split machinery `Δε`, `Δ`, `SD` used to prove Thm 7.19 and §7.3 closure properties. | `totmono_Delta_pos/_neg`, `SD`, `SD_cons`, `SnB`, `SnB_increasing`, etc. — `theories/stable/findiff.v` + `theories/stable/compose.v` |
| Lem 7.27 | If `f` is linear in arg 1 and totally monotonic in arg 2, it is totally monotonic. | `ev_totmono` (delivered in the form actually needed by the CCC) — `theories/stable/scones_ccc.v` |
| Thm 7.30 | Stable functions are closed under composition. | `stable_comp`, `meas_stable_comp` — `theories/stable/compose.v` |
| Thm 7.32 | The category `SCones` of stable functions is cartesian closed. | `SCones_ccc`, `SCones_CCC` (record + witness) — `theories/stable/scones_ccc.v` |
| Thm 7.34 | The forgetful functor `Der : ICones → SCones` preserves all limits. | `der_preserves_prod_proj`, `der_preserves_limits` — `theories/stable/der_continuous.v` |
| (also) | Stable functions admit a least-fixpoint via the cone unit-ball ω-cpo (paper §9.2). | `lfp_fixpoint`, `sfix_fixpoint`, `Yfix`, `Yfix_fix` — `theories/stable/fixpoint.v` |

The `is_stable` predicate uses `is_scott_continuous_unit` (unit-ball input,
any-radius output sup) because the strictly-linear `is_omega_continuous`
(both ω-chains in the unit ball) is **not preserved under non-negative
scaling for non-linear maps** — a faithful reading of the paper's setting,
not a weakening.

### Def 7.5 (`is_totmono`, `Pneg`, `Ppos`, `\sumP`)

```coq
(* theories/stable/totmono.v *)

(** [Pneg n] / [Ppos n] partition the subsets of {1,…,n} by parity. *)
Definition Pneg (n : nat) : {set {set 'I_n}} :=
  [set I in powerset [set: 'I_n] | odd (n - #|I|)].
Definition Ppos (n : nat) : {set {set 'I_n}} :=
  [set I in powerset [set: 'I_n] | ~~ odd (n - #|I|)].

(* [\sumP_(i in A) F] is a precone-valued indexed sum, notation. *)

(** Section variables: R : realType, P Q : coneType R. *)
Definition tm_arg (n : nat) (x : P) (u : 'I_n -> P) (I : {set 'I_n}) : P :=
  x + \big[precone_add/precone_zero]_(i in I) u i.

(** Paper Def 7.5, Condition (7.1). *)
Definition is_totmono (f : P -> Q) : Prop :=
  forall (n : nat) (x : P) (u : 'I_n -> P),
    cone_norm (x + \big[precone_add/precone_zero]_(i : 'I_n) u i) <= 1 ->
    precone_le
      (\big[precone_add/precone_zero]_(I in Pneg n) f (tm_arg x u I))
      (\big[precone_add/precone_zero]_(I in Ppos n) f (tm_arg x u I)).
```

### Def 7.7 (`is_stable`)

```coq
(* theories/stable/totmono.v *)
Definition is_stable (f : P -> Q) : Prop :=
  [/\ is_totmono f,
      exists M : R, forall x : P, cone_norm x <= 1 -> cone_norm (f x) <= M
   &  is_scott_continuous_unit f].
```

### Def 7.10 (`is_meas_stable`)

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

```coq
(* theories/stable/totmono.v *)
Lemma stable_zero : is_stable stm_zero.

Lemma stable_add (f g : P -> Q) :
  is_stable f -> is_stable g -> is_stable (stm_add f g).

Lemma stable_scale (r : {nonneg R}) (f : P -> Q) :
  is_stable f -> is_stable (stm_scale r f).
```

### Lem 7.12 (`sh_le_of_alt`)

```coq
(* theories/stable/stablehom.v *)
(** Lemma 7.12 backward: the alternating-sum order implies the pointwise
    stable (precone) order. *)
Lemma sh_le_of_alt : precone_le f g.
Proof. by exists sh_diff; rewrite -sh_add_diff. Qed.
```

### Thm 7.19 (`totmono_is_n_increasing`, `is_n_increasing_totmono`)

```coq
(* theories/stable/findiff.v *)

(** Thm 7.19 forward: totally monotonic ⇒ n-increasing for all n. *)
Lemma totmono_is_n_increasing (n : nat) (R : realType) (B C : coneType R)
    (f : B -> C) : is_totmono f -> is_n_increasing n f.

(** Thm 7.19 converse, on the closed unit ball.  Variables: R B C f. *)
Lemma is_n_increasing_totmono :
  (forall k, is_n_increasing k f) -> is_scott_continuous_unit f ->
  is_totmono f.
```

### Lem 7.20–7.25 (finite-difference Δε / Δ / SD / SnB machinery)

```coq
(* theories/stable/findiff.v + theories/stable/compose.v *)

(** [totmono_Delta]: the finite-difference [Δf(u⃗) := SDpos f − SDneg f]
    on the unit ball, packaging Δε / Δ for ε ∈ {+, −}. *)
Lemma totmono_Delta (n : nat) (u : 'I_n -> B)
    (Hs : (* sum bound on u *)) :
  (* totmono of f gives totmono of Δf(u⃗) on the residual ball *).

(** [SnB]: the "[(x, u⃗) ∈ B_n]" predicate; Lemma 7.25 says
    [(x,u⃗) ↦ Δf(u⃗)(x)] is increasing on it. *)
Definition SnB_diff (g : SnB B n) : C := (* Δf(u⃗)(x) for g = (x, u⃗) *).
Lemma SnB_increasing : is_increasing SnB_diff.
```

### Lem 7.27 (`ev_totmono`)

```coq
(* theories/stable/scones_ccc.v *)
(** Lemma 7.27: evaluation is totally monotonic on the SCones product
    [stablehom B C × B]. *)
Lemma ev_totmono : is_totmono ev_fun.
```

### Thm 7.30 (`stable_comp`, `meas_stable_comp`)

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

(** Paper Theorem 7.32: [SCones] is cartesian closed. *)
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

```coq
(* theories/stable/der_continuous.v *)

(** Paper Thm 7.34 (products): [Der] sends the [i]-th ICones projection
    to the [i]-th SCones projection (definitional). *)
Lemma der_preserves_prod_proj (i : I) :
  ders (icones_proj i) = scones_proj D i.
Proof. by []. Qed.

(** Paper Thm 7.34 (equalisers): [Der] preserves equalisers; bundled. *)
Record der_continuous : Prop := MkDerContinuous {
  dc_eq_equ : (* equaliser identity *) _;
  dc_eq_med : (* mediator with factor + uniqueness *) _;
}.

Theorem der_preserves_limits : der_continuous.
```

### §9.2 (`lfp_fixpoint`, `sfix_fixpoint`, `Yfix`, `Yfix_fix`)

```coq
(* theories/stable/fixpoint.v *)

(** [lfp f = sup uₙ] for the Kleene chain [uₙ = fⁿ 0] is a fixpoint. *)
Lemma lfp_fixpoint : f (lfp f f_incr f_ball) = lfp f f_incr f_ball.

(** [sfix f := lfp (sc_fun f) ...] is a fixpoint of the stable f. *)
Lemma sfix_fixpoint (f : scones_hom B B) : sc_fun f (sfix f) = sfix f.

(** Paper §9.2: the least-fixpoint combinator [Y] as an SCones morphism. *)
Definition Yfix : scones_hom BB B :=
  MkSconesHom (sh_fun Yfix_elt) (sh_meas_stable Yfix_elt) Yfix_norm_le1
    (sh_offball Yfix_elt).

(** Paper §9.2: the fixpoint equation [Yfix f = f (Yfix f)] on the unit ball. *)
Lemma Yfix_fix (f : BB) :
  cone_norm f <= 1 -> sh_fun f (sc_fun Yfix f) = sc_fun Yfix f.
```

---

## Paper § 9 — Linear exponential, Seely category, FMeas coalgebra

| Paper | English statement | Rocq |
|---|---|---|
| LL `!` | The linear-exponential comonad `! : ICones → ICones`, obtained as the right adjoint of `Der` via SAFT. | `Bang`, `nl`, `lin`, `lin_beta`, `lin_unique` (the adjunction data) — `theories/homs/exp_adjunction.v`; `Bang_comonad` — `theories/homs/bang.v` |
| Comonad | `(!, der, dig)` is a comonad with the standard counit / coassociativity. | `der`, `dig`, `der_prom`, `dig_prom`, the comonad laws — `theories/homs/bang.v` |
| Lem 9.4 | The natural iso `(B ⇒ₛ (C ⊸ D)) ≃ (C ⊸ (B ⇒ₛ D))` ("swap a stable outer and a linear inner"). | `stab_lin_swap` (a fully spelled-out `icones_iso`; paper gives the map + "pattern seen many times", no proof) — `theories/stable/stab_lin_swap.v` |
| Thm 9.5 | `(ICones, ⊗, 1, !)` is a **Seely category** (i.e. has the Seely isos `Seely2 : !A ⊗ !B ≃ !(A & B)` and `Seely0 : 1 ≃ !⊤`, and the comonad / SMC coherence). | `Seely2`, `Seely2E`, `Seely2_natural`, `Seely0`, `Seely0E`, the full `SeelyCategory` record + the witness `ICones_Seely` — `theories/homs/seely.v` |
| Thm 9.7 | For each `X ∈ ARCAT`, `FMeas(X)` is a `!`-coalgebra (with structure map `Coalg_X(µ) = ∫_r (δ_r)! dµ`); the assignment `X ↦ FMeas(X)` is a functor into `EM(!)`. | `Coalg`, `Coalg_dirac`, `dirac_dense`, `FMeas_coalgebra`, `FMeas_fmap` — `theories/homs/coalgebra.v` |
| Sect 9.2 | Fixpoint combinator `Y` on the cartesian closed `SCones`. | `Yfix`, `Yfix_fix` (the paper's CCC construction) — `theories/stable/fixpoint.v` |

---

## Beyond the paper — notable mathematical content we had to add

The paper *cites* a number of categorical / linear-logic results as black
boxes (SAFT, Lack's lifting, Mellies §7.4) which a textbook reader can take
on trust. A machine-checked development cannot cite a black box; the
following constructions are real mathematical content the formalisation
adds, each justified by an external reference.

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

The tensor `⊗` and the exponential `!` are then **discharged** against this
SAFT engine:

| What | Rocq |
|---|---|
| `−⊗C` is the SAFT left adjoint of `(C⊸−)` (Thm 5.9 + the SAFT engine) | `tensor_construct.v` (the tensor itself + curry/uncurry + naturality) — `theories/homs/tensor_construct.v` |
| The Thm 5.12 measurability core (the analytic crux) | `tensor_hom_iso.v` + `tensor_iso.v` (the `path_tens_to_X` / `lfun_path_swap` / `swap_lin_lin_hom` chain) |
| `E` is the SAFT left adjoint of `Der` (Thm 7.34 feeding the SAFT engine) | `der_continuous.v` (Thm 7.34) + `bang_construct.v` (Bang/nl/lin discharged) |
| The Seely isos (Thm 9.5) are discharged via Lem 9.4 + tensor-hom-iso | `theories/stable/stab_lin_swap.v` + the construction in `seely.v` |

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

### Linear/non-linear monoidal adjunction `U ⊣ !̃` (Mellies §7.4 Prop 29)

| Result | English statement | Rocq |
|---|---|---|
| LNL adjunction | The cofree-coalgebra adjunction `U ⊣ !̃ : ICones ⇄ EM(!)` is a lax symmetric monoidal adjunction (Lack's lifting). With Cor 20 in hand, this is a genuine *linear/non-linear* adjunction with the **full** category of `!`-coalgebras as the cartesian non-linear / value side. | `CBV_Model` record + `ICones_CBV` witness — `theories/homs/cbv_adjunction.v` |

### Call-by-value calculi (beyond the paper, future work)

The paper's conclusion lists *"future work: interpreting call-by-value or
call-by-push-value … languages"*. The formalisation takes a step in that
direction with two small calculi, both interpreted axiom-free.

| What | Rocq |
|---|---|
| A small first-order fine-grain Moggi-CBV calculus (unit, base, products, `let`, `sample`), interpreted via the CBV monad `T = !̃ ∘ U`; soundness includes the monad/`let` laws, product β, and `sample` = the integral. | `cbv.v` — `theories/programs/cbv.v` |
| A higher-order, direct-style, multi-variable Moggi-CBV calculus faithfully porting the QBS PPL — single-sort `expr Γ t` with intrinsically-typed De Bruijn contexts, direct application `e_app : expr Γ (tfun A B) → expr Γ A → expr Γ B`, plus `e_real`/`e_score`/`e_add`/`e_mul`. Function types via the EM(!) Kleisli exponential `!̃(U A ⊸ U B)` (no value-CCC required). Two headline examples reproduced from the [`mathcomp-qbs` `ppl` branch](https://github.com/LLM4Rocq/mathcomp-qbs/tree/ppl): `ex_random_constant` = `do c ← sample N(0,1); return (λx. c) : P(R → R)` (the QBS paper's flagship); and `ex_random_linear` = `do m, b ← N(0,1); return (λx. m·x + b)` (the killer demo — distribution over linear functions). Both interpreted axiom-free. The arithmetic primitives are interpreted via the FMeas lax-monoidal map (see next row); on Dirac inputs the lifts reduce to scalar arithmetic, and under the Moggi-Kleisli bind `bind(m, k) = ∫ k(a) dm(a)` they recover the QBS-style "distribution over deterministic linear functions" reading. | `ppl.v` (`expr`/`has_var`/`tyD`/`ctxD`/`eD`, `ex_random_constant`, `ex_random_constant_denot_E`, `ex_random_linear`, `ex_random_linear_denot_E`) — `theories/programs/ppl.v` |
| The **FMeas lax symmetric monoidal map** — `(FMeas X) ⊗ (FMeas Y) → FMeas (X × Y)`, sending the pure tensor `µ ⊗ ν` to the product measure `µ × ν` — as a genuine `icones_hom`. Built via `tensor_uncurry` of the bilinear lift; its existence depends on the previously-deferred follow-up of `bilin.v` (path-preservation of `int_to_linhom` in the cone variable), now discharged as `int_to_linhom_pres_path_in_cone`. The Dirac identity `fmeas_lax_dirac : fmeas_lax(δ_x ⊗ δ_y) = δ_{(x,y)}` is what makes the PPL's `e_add` / `e_mul` Dirac arithmetic reductions match QBS. | `fmeas_lax`, `fmeas_lax_E`, `fmeas_lax_dirac`, `int_to_linhom_pres_path_in_cone` — `theories/homs/fmeas_lax.v`, `theories/homs/bilin.v` |

The Kleisli-exponential structure arises from the natural-bijection chain

`Hom_EM(C × A, T B) ≅ Hom_IC(U(C × A), U B) ≅ Hom_IC(U C ⊗ U A, U B) ≅ Hom_IC(U C, U A ⊸ U B) ≅ Hom_EM(C, !̃(U A ⊸ U B))`

using only the cofree adjunction, `U` strict monoidal (`cbv_U_prod`), and
the SMCC closure of `ICones`. `EM(!)` is *not* cartesian closed (a
structural fact about EM categories of linear-exponential comonads, not a
missing diagram chase); Kleisli exponentials are what Moggi-CBV actually
needs, and that holds here axiom-free.

---

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

A short tour for a paper reviewer who wants to verify the headline results:

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
6. **Beyond §9** (`EMComon_all` and `ICones_CBV` in
   `theories/homs/em_cartesian.v` / `theories/homs/cbv_adjunction.v`) —
   Mellies' Cor 20 (full cartesianness of `EM(!)`) and the LNL adjunction.
7. **The CBV / PPL examples** (`cbv.v` and `ppl.v` in `theories/programs/`) —
   small calculi exercising the structure.

For deeper inspection, the `blueprint/` directory contains a
LaTeX/Patrick-Massot-style overview that mirrors this table chapter by
chapter, with clickable links to each Rocq definition.
