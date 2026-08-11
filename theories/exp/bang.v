(**md**************************************************************************)
(** * The exponential comonad [!] on [ICones] — Paper §9

    From the linear/non-linear adjunction [E ⊣ Der]
    ([theories/homs/exp_adjunction.v], built on [bang_construct.v]) we
    DERIVE — as genuine theorems — the exponential comonad [(!, der, dig)]
    of paper §9, the model of the [!] modality of [LL].

    [exp_adjunction.v] exposes the object map [Bang = E = !], the unit
    [nl B : B → !B] (the universal nonlinear map [\Unistab_B]), the linear
    factoriser [lin], and the two halves of the universal property of
    [nl_B] ([lin_beta]/[lin_unique]).  Everything below is built from
    these by the natural bijection

      [Θ : icones_hom (!B) C ≃ scones_hom B C],   [Θ h := ders h ∘ nl_B].

    Contents:
    - [Theta]/[ThetaK]/[linK] — the hom-bijection [Θ] and that [Θ]/[lin]
      are mutually inverse.
    - [prom] ([x!]) — the promoted point [x! = nl_B(x)], with the
      pointwise reading [Theta_prom] of [Θ] on the unit ball.
    - [bang_ext] (Lemma [tens-excl-equal-charact], [n=1]) — linear maps
      out of [!B] agreeing on all [x!] are equal — the workhorse lemma.
    - [bang_fmap] ([!f = E(Der f)]) with [bang_fmap_prom] (Lemma
      [excl-fun-prom]: [(!f)(x!) = (f x)!]) and the functor laws
      [bang_fmap_id]/[bang_fmap_comp].
    - [der] (counit, [der_B(x!) = x]) with naturality [der_nat], and
      [dig] (comultiplication [= E(nl_B)], [dig_B(x!) = x!!]) with
      naturality [dig_nat].
    - the comonad laws [comonad_counitL]/[comonad_counitR]/
      [comonad_coassoc], each reduced to promoted points by [bang_ext].
    - the [Comonad] record and the witness [Bang_comonad] (mirroring
      [ICones_SMCC] of [smcc.v]).

    Paper reference: §9, lines for [E ⊣ Der], the bijection [Θ], the unit
    [nl], the comonad via co-Kleisli, the counit [der], the
    comultiplication [dig = E(nl)], and the Lemmas [tens-excl-equal-charact]
    ([n=1]) and [excl-fun-prom].

    All results are THEOREMS; verified [Print Assumptions Bang_comonad]
    = the three classical [boolp] axioms only. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.reals Require Import reals.

Require Import Icones.cones.precone.
Require Import Icones.cones.cone.
Require Import Icones.cones.cone_cat.
Require Import Icones.mcones.ar.
Require Import Icones.mcones.mcone.
Require Import Icones.mcones.mcone_cat.
Require Import Icones.icones.icone.
Require Import Icones.icones.icone_cat.
Require Import Icones.stable.scones_cat.
Require Import Icones.homs.exp_adjunction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Bang.
Variables (R : realType) (Ar : MeasSubcat R).

(** The underlying linear function of an [icones_hom] — the same coercion
    chain used by [icones_hom_eq] and by [ders] ([scones_cat.v]). *)
Local Notation Lfun h := (cones_hom_fun (mcones_hom_cones (icones_hom_mcones h))).

(** ** The hom-bijection [Θ] — Paper §9

    [Θ h := ders h ∘ nl_B], a [scones_hom B C].  Its inverse is
    [lin]. *)

Definition Theta (B C : ICone.type Ar) (h : icones_hom Ar (Bang Ar B) C) :
    scones_hom B C :=
  scones_comp (ders h) (nl B).

(** [Θ (lin f) = f] — directly the existence half [lin_beta]. *)
Lemma ThetaK (B C : ICone.type Ar) (f : scones_hom B C) :
  Theta (lin f) = f.
Proof. exact: lin_beta. Qed.

(** [lin (Θ h) = h] — the uniqueness half with [f := Θ h]. *)
Lemma linK (B C : ICone.type Ar) (h : icones_hom Ar (Bang Ar B) C) :
  lin (Theta h) = h.
Proof. exact/esym/(lin_unique (Theta h) h erefl). Qed.

(** ** Promotion [x!] — Paper §9, [\Proms x]

    [prom B x = nl_B(x)], the promoted point.  For [‖x‖ ≤ 1] the unit
    [nl_B] has norm [≤ 1], so [‖x!‖ ≤ 1] ([prom_ball]). *)

Definition prom (B : ICone.type Ar) (x : B) : Bang Ar B := sc_fun (nl B) x.

Local Notation "x '!'" := (prom x) (at level 2, format "x '!'").

(** For [‖x‖ ≤ 1], the promoted point [x!] is in the unit ball of [!B]. *)
Lemma prom_ball (B : ICone.type Ar) (x : B) :
  cone_norm x <= 1 -> cone_norm (prom x) <= 1.
Proof. exact: (sc_image_ball (nl B)). Qed.

(** **Pointwise reading of [Θ].**  For [‖x‖ ≤ 1],
    [Θ h (x) = (Lfun h)(x!)].  Unfold [scones_comp] on the ball: the
    outer clamp is transparent there; [ders h] applied to [x!] is its
    clamp of [Lfun h], transparent again since [x!] is in the ball. *)
Lemma Theta_prom (B C : ICone.type Ar)
    (h : icones_hom Ar (Bang Ar B) C) (x : B) :
  cone_norm x <= 1 -> sc_fun (Theta h) x = Lfun h x!.
Proof.
move=> Hx; rewrite /Theta /= (sc_clamp_ball Hx) /ders /=.
by rewrite (sc_clamp_ball (prom_ball Hx)).
Qed.

(** ** Extensionality — Paper Lemma [tens-excl-equal-charact] ([n=1])

    Linear maps [f g : !B → C] agreeing on all promoted points [x!]
    (for [‖x‖ ≤ 1]) are equal.  The hypothesis makes [Θ f] and [Θ g]
    agree everywhere ([scones_hom_eq]: on the ball by [Theta_prom] + the
    hypothesis, off the ball both are [0] by the [scones_comp]
    0-extension), so [f = lin (Θ f) = lin (Θ g) = g] by [linK].

    The workhorse for every comonad law below. *)
Lemma bang_ext (B C : ICone.type Ar) (f g : icones_hom Ar (Bang Ar B) C) :
  (forall x : B, cone_norm x <= 1 -> Lfun f x! = Lfun g x!) ->
  f = g.
Proof.
move=> Hfg; rewrite -(linK f) -(linK g); congr lin.
apply: scones_hom_eq => x.
have [Hx | Hx] := boolP (cone_norm x <= 1).
  by rewrite !Theta_prom//; exact: Hfg.
by rewrite /Theta /= !(sc_clamp_offball Hx).
Qed.

(** ** Functoriality of [!] — Paper §9

    [!f = E(Der f) = lin (nl_C ∘ ders f)], the action of the comonad on
    morphisms. *)
Definition bang_fmap (B C : ICone.type Ar) (f : icones_hom Ar B C) :
    icones_hom Ar (Bang Ar B) (Bang Ar C) :=
  lin (scones_comp (nl C) (ders f)).

(** **Lemma [excl-fun-prom]: [(!f)(x!) = (f x)!]** for [‖x‖ ≤ 1].

    [ders (!f) ∘ nl_B = Θ(!f) = nl_C ∘ ders f] by [ThetaK]; evaluate at
    [x] through [Theta_prom] (LHS) and unfold the composite [nl_C ∘ ders f]
    on the ball (RHS), where [ders f] is [Lfun f x] (in the ball since
    [f] is norm-[≤ 1]) and [nl_C] of it is [(f x)!]. *)
Lemma bang_fmap_prom (B C : ICone.type Ar) (f : icones_hom Ar B C) (x : B) :
  cone_norm x <= 1 -> Lfun (bang_fmap f) x! = prom (Lfun f x).
Proof.
move=> Hx; have := ThetaK (B := B) (C := Bang Ar C) (scones_comp (nl C) (ders f)).
rewrite -/(bang_fmap f) => /(congr1 (fun h : scones_hom B (Bang Ar C) => sc_fun h x)).
rewrite (Theta_prom (bang_fmap f) Hx) /= (sc_clamp_ball Hx) => ->.
rewrite /ders /= (sc_clamp_ball Hx).
by rewrite /prom.
Qed.

(** [!] preserves identities: on [x!], [(!id)(x!) = (id x)! = x!]. *)
Lemma bang_fmap_id (B : ICone.type Ar) :
  bang_fmap (icones_id Ar B) = icones_id Ar (Bang Ar B).
Proof.
apply: bang_ext => x Hx.
by rewrite (bang_fmap_prom (icones_id Ar B) Hx).
Qed.

(** [!] preserves composition: on [x!], both sides give [(g (f x))!]. *)
Lemma bang_fmap_comp (B C D : ICone.type Ar)
    (g : icones_hom Ar C D) (f : icones_hom Ar B C) :
  bang_fmap (icones_comp g f) =
  icones_comp (bang_fmap g) (bang_fmap f).
Proof.
apply: bang_ext => x Hx.
rewrite (bang_fmap_prom (icones_comp g f) Hx) /=.
rewrite (bang_fmap_prom f Hx).
by rewrite (bang_fmap_prom g (ders_lin_ball f Hx)).
Qed.

(** ** Counit [der] — Paper §9, [\Ders_B]

    [der B = lin (id_B)], the dereliction.  [Θ(der B) = id_B], so
    [der_B(x!) = x] for [‖x‖ ≤ 1]. *)
Definition der (B : ICone.type Ar) : icones_hom Ar (Bang Ar B) B :=
  lin (scones_id B).

(** [der_B(x!) = x] for [‖x‖ ≤ 1] ([Θ(der B) = id], evaluated at [x]). *)
Lemma der_prom (B : ICone.type Ar) (x : B) :
  cone_norm x <= 1 -> Lfun (der B) x! = x.
Proof.
move=> Hx; have := ThetaK (B := B) (C := B) (scones_id B).
rewrite -/(der B) => /(congr1 (fun h : scones_hom B B => sc_fun h x)).
by rewrite (Theta_prom (der B) Hx) /= (sc_clamp_ball Hx) => ->.
Qed.

(** ** Norm of promotion — partial results

    The exact identity [cone_norm (prom x) = cone_norm x] DOES NOT hold
    in general: the wide-intersection [Bang B] norm is the sup over the
    factoring family of the cone-norms of the witness maps' images, and
    generic stable witnesses (totally monotone + measurable, but NOT
    homogeneous) can grow the cone-norm of sub-unit-ball points (cf.
    [c1_norm] readings of non-homogeneous stable maps [j : B → Cone1] —
    these are admissible family members).

    What IS provable, axiom-free:

    1. [prom_norm_ge] : [‖x‖ ≤ 1 ⇒ ‖x‖ ≤ ‖x!‖].  Promotion never
       shrinks the cone-norm on the unit ball.  From [der_prom] +
       linearity of [der] ([cones_hom_norm_le1]): [‖x‖ = ‖der(x!)‖ ≤
       ‖x!‖].

    2. [prom_norm_one] : [‖x‖ = 1 ⇒ ‖x!‖ = 1].  Promotion preserves
       unit mass.  Combine [prom_ball] (upper bound [≤ 1]) with
       [prom_norm_ge] (lower bound [≥ ‖x‖ = 1]).

    The full equality [‖x!‖ = ‖x‖] for [0 < ‖x‖ < 1] is OPEN and would
    require either positive-homogeneity of [nl_B] (which fails: [nl_B]
    is the universal NONLINEAR map) or an upper-bound mechanism beyond
    [prom_ball].  *)

(** [‖x‖ ≤ ‖x!‖] for [‖x‖ ≤ 1].

    [der_B] is a linear (cones) morphism of operator norm [≤ 1]
    ([cones_hom_norm_le1]).  [der_prom] gives [der_B(x!) = x], so
    [‖x‖ = ‖der_B(x!)‖ ≤ ‖x!‖]. *)
Lemma prom_norm_ge (B : ICone.type Ar) (x : B) :
  cone_norm x <= 1 -> cone_norm x <= cone_norm (prom x).
Proof.
move=> Hx.
have Hder := cones_hom_norm_le1
               (mcones_hom_cones (icones_hom_mcones (der B))) (prom x).
by rewrite (der_prom Hx) in Hder.
Qed.

(** [‖x‖ = 1 ⇒ ‖x!‖ = 1].  Promotion preserves unit mass.

    Antisymmetry from [prom_ball] ([‖x!‖ ≤ 1]) and [prom_norm_ge]
    ([1 = ‖x‖ ≤ ‖x!‖]). *)
Lemma prom_norm_one (B : ICone.type Ar) (x : B) :
  cone_norm x = 1 -> cone_norm (prom x) = 1.
Proof.
move=> Hx; apply: le_anti; apply/andP; split.
  by apply: prom_ball; rewrite Hx.
by rewrite -[X in X <= _]Hx; apply: prom_norm_ge; rewrite Hx.
Qed.

(** Naturality of the counit: [f ∘ der_B = der_C ∘ !f].  On [x!]: LHS
    is [f(der_B(x!)) = f x]; RHS is [der_C((!f)(x!)) = der_C((f x)!) =
    f x]. *)
Lemma der_nat (B C : ICone.type Ar) (f : icones_hom Ar B C) :
  icones_comp f (der B) = icones_comp (der C) (bang_fmap f).
Proof.
apply: bang_ext => x Hx; rewrite /= (der_prom Hx).
rewrite (bang_fmap_prom f Hx).
by rewrite (der_prom (ders_lin_ball f Hx)).
Qed.

(** ** Comultiplication [dig] — Paper §9, [\Diggs_B = E(nl_B)]

    [dig B = lin (nl_{!B} ∘ nl_B)].  [Θ(dig B) = nl_{!B} ∘ nl_B], so
    [dig_B(x!) = (x!)! = x!!] for [‖x‖ ≤ 1]. *)
Definition dig (B : ICone.type Ar) :
    icones_hom Ar (Bang Ar B) (Bang Ar (Bang Ar B)) :=
  lin (scones_comp (nl (Bang Ar B)) (nl B)).

(** [dig_B(x!) = (x!)!] for [‖x‖ ≤ 1] ([Θ(dig B) = nl_{!B} ∘ nl_B],
    evaluated at [x]; [nl_B(x) = x!] is in the ball). *)
Lemma dig_prom (B : ICone.type Ar) (x : B) :
  cone_norm x <= 1 -> Lfun (dig B) x! = prom (prom x).
Proof.
move=> Hx.
have := ThetaK (B := B) (C := Bang Ar (Bang Ar B))
  (scones_comp (nl (Bang Ar B)) (nl B)).
rewrite -/(dig B) => /(congr1
  (fun h : scones_hom B (Bang Ar (Bang Ar B)) => sc_fun h x)).
rewrite (Theta_prom (dig B) Hx) /= (sc_clamp_ball Hx) => ->.
by rewrite /prom.
Qed.

(** Naturality of the comultiplication: [!!f ∘ dig_B = dig_C ∘ !f].
    On [x!]: LHS is [(!!f)((x!)!) = ((!f)(x!))! = ((f x)!)!]; RHS is
    [dig_C((!f)(x!)) = dig_C((f x)!) = ((f x)!)!]. *)
Lemma dig_nat (B C : ICone.type Ar) (f : icones_hom Ar B C) :
  icones_comp (bang_fmap (bang_fmap f)) (dig B) =
  icones_comp (dig C) (bang_fmap f).
Proof.
apply: bang_ext => x Hx; rewrite /= (dig_prom Hx).
rewrite (bang_fmap_prom (bang_fmap f) (prom_ball Hx)).
rewrite (bang_fmap_prom f Hx).
by rewrite (dig_prom (ders_lin_ball f Hx)).
Qed.

(** ** The comonad laws — Paper §9 *)

(** Left counit [der_{!B} ∘ dig_B = id_{!B}].  On [x!]:
    [der_{!B}(dig_B(x!)) = der_{!B}((x!)!) = x!]. *)
Lemma comonad_counitL (B : ICone.type Ar) :
  icones_comp (der (Bang Ar B)) (dig B) = icones_id Ar (Bang Ar B).
Proof.
apply: bang_ext => x Hx; rewrite /= (dig_prom Hx).
by rewrite (der_prom (prom_ball Hx)).
Qed.

(** Right counit [!(der_B) ∘ dig_B = id_{!B}].  On [x!]:
    [(!der_B)(dig_B(x!)) = (!der_B)((x!)!) = (der_B(x!))! = x!]. *)
Lemma comonad_counitR (B : ICone.type Ar) :
  icones_comp (bang_fmap (der B)) (dig B) = icones_id Ar (Bang Ar B).
Proof.
apply: bang_ext => x Hx; rewrite /= (dig_prom Hx).
rewrite (bang_fmap_prom (der B) (prom_ball Hx)).
by rewrite (der_prom Hx).
Qed.

(** Coassociativity [dig_{!B} ∘ dig_B = !(dig_B) ∘ dig_B].  On [x!]:
    LHS is [dig_{!B}(dig_B(x!)) = dig_{!B}((x!)!) = ((x!)!)!];
    RHS is [(!dig_B)(dig_B(x!)) = (!dig_B)((x!)!) = (dig_B(x!))! =
    ((x!)!)!]. *)
Lemma comonad_coassoc (B : ICone.type Ar) :
  icones_comp (dig (Bang Ar B)) (dig B) =
  icones_comp (bang_fmap (dig B)) (dig B).
Proof.
apply: bang_ext => x Hx; rewrite /= (dig_prom Hx).
rewrite (dig_prom (prom_ball Hx)).
rewrite (bang_fmap_prom (dig B) (prom_ball Hx)).
by rewrite (dig_prom Hx).
Qed.

End Bang.

Arguments Theta {R Ar B C}.
Arguments ThetaK {R Ar B C}.
Arguments linK {R Ar B C}.
Arguments prom {R Ar B}.
Arguments prom_ball {R Ar B x}.
Arguments Theta_prom {R Ar B C} h x.
Arguments bang_ext {R Ar B C}.
Arguments bang_fmap {R Ar B C}.
Arguments bang_fmap_prom {R Ar B C} f x.
Arguments bang_fmap_id {R Ar} B.
Arguments bang_fmap_comp {R Ar B C D}.
Arguments der {R Ar} B.
Arguments der_prom {R Ar B} x.
Arguments prom_norm_ge {R Ar B} x.
Arguments prom_norm_one {R Ar B} x.
Arguments der_nat {R Ar B C}.
Arguments dig {R Ar} B.
Arguments dig_prom {R Ar B} x.
Arguments dig_nat {R Ar B C}.
Arguments comonad_counitL {R Ar} B.
Arguments comonad_counitR {R Ar} B.
Arguments comonad_coassoc {R Ar} B.

(** ** The comonad record — Paper §9

    Package the object map, the functorial action, the counit and the
    comultiplication together with the five comonad laws (functor
    identity/composition, the two counit laws, coassociativity), mirroring
    [ICones_SMCC] of [smcc.v].  The canonical witness [Bang_comonad]
    populates every field with the proved lemmas above. *)

Record Comonad (R : realType) (Ar : MeasSubcat R) : Type :=
  MkComonad {
  cm_obj : ICone.type Ar -> ICone.type Ar;
  cm_fmap : forall B C : ICone.type Ar,
    icones_hom Ar B C -> icones_hom Ar (cm_obj B) (cm_obj C);
  cm_der : forall B : ICone.type Ar, icones_hom Ar (cm_obj B) B;
  cm_dig : forall B : ICone.type Ar,
    icones_hom Ar (cm_obj B) (cm_obj (cm_obj B));
  (* functor laws *)
  cm_fmap_id : forall B : ICone.type Ar,
    cm_fmap (icones_id Ar B) = icones_id Ar (cm_obj B);
  cm_fmap_comp : forall (B C D : ICone.type Ar)
    (g : icones_hom Ar C D) (f : icones_hom Ar B C),
    cm_fmap (icones_comp g f) = icones_comp (cm_fmap g) (cm_fmap f);
  (* comonad laws *)
  cm_counitL : forall B : ICone.type Ar,
    icones_comp (cm_der (cm_obj B)) (cm_dig B) = icones_id Ar (cm_obj B);
  cm_counitR : forall B : ICone.type Ar,
    icones_comp (cm_fmap (cm_der B)) (cm_dig B) = icones_id Ar (cm_obj B);
  cm_coassoc : forall B : ICone.type Ar,
    icones_comp (cm_dig (cm_obj B)) (cm_dig B) =
    icones_comp (cm_fmap (cm_dig B)) (cm_dig B);
}.

Arguments Comonad {R} Ar.

(** Paper §9: the exponential comonad [!] on [ICones], every field
    populated by a proved lemma (axiom-free). *)
Definition Bang_comonad (R : realType) (Ar : MeasSubcat R) : Comonad Ar :=
  {| cm_obj := @Bang R Ar;
     cm_fmap := @bang_fmap R Ar;
     cm_der := @der R Ar;
     cm_dig := @dig R Ar;
     cm_fmap_id := @bang_fmap_id R Ar;
     cm_fmap_comp := @bang_fmap_comp R Ar;
     cm_counitL := @comonad_counitL R Ar;
     cm_counitR := @comonad_counitR R Ar;
     cm_coassoc := @comonad_coassoc R Ar |}.
