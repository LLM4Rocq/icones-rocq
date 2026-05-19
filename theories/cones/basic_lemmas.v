(** * Basic properties of cones — Paper §2.3

    This file develops the algebraic properties of linear and
    ω-continuous maps between cones (paper Lemmas 2.8–2.10, with
    Lemma 2.11 partly stated). The two workhorse definitions are
    [is_linear] (paper §2.1) and [is_omega_continuous] (paper §2.1).

    Paper reference: §2.3 (page 1:13), Basic properties.

    Coverage in this file:
    - [is_linear], [is_increasing], [is_omega_continuous] definitions.
    - Lemma 2.8 (inverse of linear ω-continuous bijection).
    - Lemma 2.9 (addition and scalar multiplication are increasing and
      ω-continuous in each argument), together with the workhorse
      identities [sup_ball_addr] and [sup_ball_scaler].
    - Lemma 2.10 (ω-continuity of differences) in its conditional
      unit-ball-chain form.
    - Lemma 2.11 (operator-norm boundedness) is *deferred* with full
      documentation of the partial-sum proof structure and the
      partial-sum machinery [pcone_sum], [pcone_sum_norm_le]; the
      arithmetic plumbing of the [(4^n)/(2^{n+1}) = 2^{n-1}]
      contradiction is left to a follow-up (consumed by [cone_cat.v]).

    Design notes.
    - [is_linear] is a conjunctive [Prop]-record, [is_omega_continuous]
      is a single proposition quantifying over chains in the unit ball.
      We keep both as plain [Prop] (no HB structure on functions) because
      Lemma 2.8 manipulates them point-wise.
    - The "ω-continuous" predicate is a property *of* a function
      [f : P -> Q] alone; the chain conditions in the conclusion are
      passed as additional hypotheses to dodge the [B_P → B_Q] mismatch
      (a function increasing on [B_P] need not map [B_P] into [B_Q]).
      Lemma 2.9, applied to [λ x. x + y] with [‖y‖ > 0], illustrates the
      need: we cannot conclude [f] is ω-continuous as a unit-ball
      endomap, only as a partial commutation with [cone_sup_ball] *when
      the image chain is also in the unit ball*.
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.reals Require Import reals.
From mathcomp.algebra Require Import interval_inference archimedean.

Require Import Icones.prelude.classical_extra.
Require Import Icones.prelude.nonneg_extra.
Require Import Icones.prelude.omegacpo.
Require Import Icones.cones.precone.
Require Import Icones.cones.cone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(** ** Linear and increasing maps *)

Section LinearMaps.
Variable R : realType.
Variables P Q : preconeType R.

(** Paper §2.1: a function [f : P -> Q] is *linear* iff it preserves
    [0], [+], and scalar multiplication. *)
Record is_linear (f : P -> Q) : Prop := IsLinear {
  linear0 : f precone_zero = precone_zero;
  linearD : forall x y, f (precone_add x y) = precone_add (f x) (f y);
  linearZ : forall (r : {nonneg R}) x,
    f (precone_scale r x) = precone_scale r (f x);
}.

(** Paper §2.1: [f] is *increasing* iff it preserves the cone order. *)
Definition is_increasing (f : P -> Q) : Prop :=
  forall x y, precone_le x y -> precone_le (f x) (f y).

(** A linear map is increasing: if [y = x + z] then [f y = f x + f z]. *)
Lemma linear_increasing (f : P -> Q) :
  is_linear f -> is_increasing f.
Proof.
move=> Hf x y [z ->]; exists (f z); exact: linearD.
Qed.

End LinearMaps.

Arguments is_linear {R P Q}.
Arguments is_increasing {R P Q}.

(** ** ω-continuous maps

    A function [f : P -> Q] between cones is *ω-continuous* when, for
    every increasing chain [u] in the unit ball [B_P] whose image [f ∘
    u] is also an increasing chain in [B_Q], the supremum of [f ∘ u]
    in [B_Q] coincides with [f] of the supremum of [u] in [B_P]. The
    image-chain hypotheses are passed explicitly: the cleanest user
    interface is via the wrapper [omega_continuous_apply] below. *)

Section OmegaContinuous.
Variable R : realType.
Variables P Q : coneType R.

(** Paper §2.1: [f] is ω-continuous on the unit ball. *)
Definition is_omega_continuous (f : P -> Q) : Prop :=
  forall (u : nat -> P)
         (uch : forall n, precone_le (u n) (u n.+1))
         (ub1 : forall n, cone_norm (u n) <= 1)
         (fuch : forall n, precone_le (f (u n)) (f (u n.+1)))
         (fub1 : forall n, cone_norm (f (u n)) <= 1),
    f (cone_sup_ball u uch ub1) = cone_sup_ball (f \o u) fuch fub1.

End OmegaContinuous.

Arguments is_omega_continuous {R P Q}.

(** ** Paper Lemma 2.8 — inversion of linear ω-continuous bijections *)

Section Lemma28.
Variable R : realType.
Variables P Q : coneType R.

(** Paper Lemma 2.8: if [f] is linear, ω-continuous, and bijective, then
    [f^{-1}] is linear and ω-continuous.

    We isolate the construction of the inverse via [cid] (constructive
    indefinite description applied to the surjectivity witness). *)

Variable f : P -> Q.
Hypothesis Hlin  : is_linear f.
Hypothesis Hcont : is_omega_continuous f.
Hypothesis Hinj  : injective f.
Hypothesis Hsurj : forall y : Q, exists x : P, f x = y.

(** The constructive inverse, extracted from surjectivity. *)
Definition invf (y : Q) : P := projT1 (cid (Hsurj y)).

Lemma invfK : forall y, f (invf y) = y.
Proof. by move=> y; exact: projT2 (cid (Hsurj y)). Qed.

Lemma invKf : forall x, invf (f x) = x.
Proof. by move=> x; apply: Hinj; rewrite invfK. Qed.

(** Paper Lemma 2.8, first half: [invf] is linear.

    Proof. By injectivity of [f], applied after rewriting with [f
    (invf y) = y] and the linearity of [f]. *)
Lemma invf_linear : is_linear invf.
Proof.
split.
- apply: Hinj; rewrite invfK; symmetry; exact: linear0 Hlin.
- move=> y1 y2; apply: Hinj.
  rewrite invfK (linearD Hlin) !invfK //.
- move=> r y; apply: Hinj.
  rewrite invfK (linearZ Hlin) invfK //.
Qed.

(** [invf] is increasing as a corollary of linearity. *)
Lemma invf_increasing : is_increasing invf.
Proof. exact: linear_increasing invf_linear. Qed.

(** Paper Lemma 2.8, second half: [invf] is ω-continuous.

    Proof sketch. Let [(y_n)] be increasing in [B_Q] with image
    chain [(invf y_n)] in [B_P], with sup [y]. Since [invf] is
    increasing, [(invf y_n)] is increasing; by hypothesis it is in
    [B_P]. Let [x] be its sup. We must show [x = invf y]. By
    [cone_sup_ball_lub], [x ≤p invf y]. Conversely, by continuity of
    [f], [f x = sup (f ∘ invf ∘ y_n) = sup y_n = y], so [x = invf y]
    by injectivity of [f]. *)
Lemma invf_omega_continuous : is_omega_continuous invf.
Proof.
rewrite /is_omega_continuous => u uch ub1 vuch vub1.
set x := cone_sup_ball (fun n => invf (u n)) vuch vub1.
set y := cone_sup_ball u uch ub1.
(* By continuity of [f] on the chain [fun n => invf (u n)]. *)
have fch : forall n, precone_le (f (invf (u n))) (f (invf (u n.+1))).
  by move=> n; rewrite !invfK; exact: uch.
have fub : forall n, cone_norm (f (invf (u n))) <= 1.
  by move=> n; rewrite invfK; exact: ub1.
have Hfx : f x = cone_sup_ball (f \o (fun n => invf (u n))) fch fub.
  rewrite /x.
  move: Hcont; rewrite /is_omega_continuous => Hcont'.
  exact: Hcont'.
(* The sequence [f \o invf \o u] coincides pointwise with [u]. *)
have Hfx_eq_y : f x = y.
  apply: precone_le_anti.
  - rewrite Hfx; apply: cone_sup_ball_lub => n.
    rewrite /= invfK; exact: cone_sup_ball_ub.
  - rewrite Hfx; apply: cone_sup_ball_lub => n.
    have ->: u n = (f \o (fun n => invf (u n))) n by rewrite /= invfK.
    exact: cone_sup_ball_ub.
by apply: Hinj; rewrite Hfx_eq_y invfK.
Qed.

End Lemma28.

(** ** Paper Lemma 2.9 — addition and scalar multiplication are
       increasing and ω-continuous *)

Section Lemma29.
Variable R : realType.
Variable P : coneType R.
Implicit Types (x y : P) (r s : {nonneg R}).

(** Paper Lemma 2.9: addition is increasing in each argument. *)
Lemma addr_increasing y : is_increasing (fun x : P => precone_add x y).
Proof. by move=> x1 x2; exact: precone_add_le_r. Qed.

Lemma addl_increasing x : is_increasing (fun y : P => precone_add x y).
Proof. by move=> y1 y2; exact: precone_add_le_l. Qed.

(** Paper Lemma 2.9: scalar multiplication is increasing in its
    vector argument. *)
Lemma scaler_increasing r : is_increasing (fun x : P => precone_scale r x).
Proof. by move=> x1 x2; exact: precone_scale_le. Qed.

(** ω-continuity of addition in the first argument.

    Given an increasing unit-ball chain [u] and a fixed [y] in [P]
    such that the chain [n ↦ u n + y] is also in the unit ball, we
    have [sup (u + y) = (sup u) + y].

    Proof. By antisymmetry of the cone order.

    - [sup (u + y) ≤p (sup u) + y]: by [cone_sup_ball_lub], it
      suffices to show [u n + y ≤p (sup u) + y] for every [n],
      which is [precone_add_le_r] applied to [u n ≤p sup u].

    - [(sup u) + y ≤p sup (u + y)] is the hard direction. We
      use [cid] to extract, for each [n], a witness [w_n] with
      [sup (u + y) = (u n + y) + w_n]. Then for all [m, n] we have
      [u n + w_n = u m + w_m] (cancel [y], use commutativity, and
      cancel [u m]/[u n] mod [precone_cancel]). Setting [a := u 0 + w_0],
      the chain [u] is bounded above by [a], so [sup u ≤p a],
      giving [a = sup u + z] for some [z]. Then
      [sup (u + y) = u 0 + y + w_0 = a + y = (sup u + z) + y =
       (sup u + y) + z]. *)

(** Helper: any chain [u + y] in [B_P] satisfies
    [sup_ball (u + y) = (sup_ball u) + y]. We prove it as a single
    equality, then use it for ω-continuity. *)
Lemma sup_ball_addr (u : nat -> P)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, cone_norm (u n) <= 1)
  (y : P)
  (fuch : forall n, precone_le (precone_add (u n) y) (precone_add (u n.+1) y))
  (fub1 : forall n, cone_norm (precone_add (u n) y) <= 1) :
  cone_sup_ball (fun n => precone_add (u n) y) fuch fub1 =
  precone_add (cone_sup_ball u uch ub1) y.
Proof.
set s  := cone_sup_ball (fun n => precone_add (u n) y) fuch fub1.
set su := cone_sup_ball u uch ub1.
(* Direction 1: s ≤p su + y. *)
have Dir1 : precone_le s (precone_add su y).
  apply: cone_sup_ball_lub => n.
  by apply: precone_add_le_r; exact: cone_sup_ball_ub.
(* Direction 2: su + y ≤p s. Build via witness. *)
have Dir2 : precone_le (precone_add su y) s.
  (* Witnesses w_n with [s = (u n + y) + w_n]. *)
  have wsex : forall n, exists w, s = precone_add (precone_add (u n) y) w.
    move=> n.
    by have := cone_sup_ball_ub (fun n => precone_add (u n) y) fuch fub1 n.
  pose ws (n : nat) : P := projT1 (cid (wsex n)).
  have ws_eq : forall n, s = precone_add (precone_add (u n) y) (ws n).
    by move=> n; exact: projT2 (cid (wsex n)).
  (* All u n + w n equal u 0 + w 0. *)
  have u_w_const : forall n,
      precone_add (u n) (ws n) = precone_add (u 0) (ws 0).
    move=> n.
    have H0 : s = precone_add (precone_add (u 0) (ws 0)) y.
      by rewrite (ws_eq 0) -precone_addA (precone_addC y (ws 0)) precone_addA.
    have Hn : s = precone_add (precone_add (u n) (ws n)) y.
      by rewrite (ws_eq n) -precone_addA (precone_addC y (ws n)) precone_addA.
    have HH : precone_add (precone_add (u 0) (ws 0)) y =
              precone_add (precone_add (u n) (ws n)) y.
      by rewrite -H0.
    by symmetry; apply: precone_cancelr HH.
  (* u n ≤p u 0 + w 0 for all n. *)
  have Hu_bnd : forall n, precone_le (u n) (precone_add (u 0) (ws 0)).
    by move=> n; rewrite -(u_w_const n); exists (ws n).
  (* su ≤p u 0 + w 0. *)
  have [z Hz] : precone_le su (precone_add (u 0) (ws 0)).
    by apply: cone_sup_ball_lub.
  (* Hz : u 0 + w 0 = su + z. Then
     s = (u 0 + y) + w 0 = (u 0 + w 0) + y = (su + z) + y =
     (su + y) + z. *)
  exists z.
  rewrite (ws_eq 0).
  rewrite -[in LHS]precone_addA (precone_addC y (ws 0)) precone_addA.
  rewrite Hz.
  rewrite -[in RHS]precone_addA (precone_addC y z) precone_addA //.
by apply: precone_le_anti.
Qed.

(** Paper Lemma 2.9: addition is ω-continuous in the first argument
    (whenever the image chain stays in the unit ball). *)
Lemma addr_omega_continuous y :
  is_omega_continuous (fun x : P => precone_add x y).
Proof.
rewrite /is_omega_continuous => u uch ub1 fuch fub1.
by rewrite (@sup_ball_addr u uch ub1 y fuch fub1).
Qed.

Lemma addl_omega_continuous x :
  is_omega_continuous (fun y : P => precone_add x y).
Proof.
rewrite /is_omega_continuous => u uch ub1 fuch fub1.
(* Symmetric: rewrite x + u_n as u_n + x, apply [sup_ball_addr]. *)
have fuch' : forall n,
    precone_le (precone_add (u n) x) (precone_add (u n.+1) x).
  by move=> n; rewrite -!(precone_addC x); exact: fuch.
have fub1' : forall n, cone_norm (precone_add (u n) x) <= 1.
  by move=> n; rewrite precone_addC; exact: fub1.
(* LHS is sup_ball (fun n => x + u n) fuch fub1.
   First swap the chain to sup_ball (fun n => u n + x) fuch' fub1'. *)
have swap_eq : cone_sup_ball (fun n => precone_add x (u n)) fuch fub1 =
               cone_sup_ball (fun n => precone_add (u n) x) fuch' fub1'.
  apply: precone_le_anti.
  - apply: cone_sup_ball_lub => n /=.
    have -> : precone_add x (u n) = precone_add (u n) x by rewrite precone_addC.
    exact: cone_sup_ball_ub.
  - apply: cone_sup_ball_lub => n /=.
    have -> : precone_add (u n) x = precone_add x (u n) by rewrite precone_addC.
    exact: cone_sup_ball_ub.
rewrite swap_eq.
rewrite (@sup_ball_addr u uch ub1 x fuch' fub1').
by rewrite precone_addC.
Qed.

(** ω-continuity of scalar multiplication in the vector argument.

    [r *: (sup u) = sup (r *: u_n)] whenever the image chain stays
    in the unit ball.

    Proof. By antisymmetry. [sup (r *: u) ≤p r *: sup u] is by
    [cone_sup_ball_lub] and [precone_scale_le].

    For the reverse direction we case-split on [r = 0]: when [r = 0]
    the LHS is [0] and the conclusion is trivial. When [r > 0] we
    use the inverse [rinv := r^{-1} : {nonneg R}], so that
    [rinv *: r *: x = x]. Apply [rinv *: -] to [s = r *: u_n + w_n]
    (witnesses of [r *: u_n ≤p s]): we get [rinv *: s = u_n + rinv *: w_n],
    hence [u_n ≤p rinv *: s] uniformly in [n]. So [su ≤p rinv *: s],
    say [rinv *: s = su + z], and scaling back, [s = r *: su + r *: z],
    giving [r *: su ≤p s]. *)
Lemma sup_ball_scaler (r : {nonneg R}) (u : nat -> P)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, cone_norm (u n) <= 1)
  (fuch : forall n,
      precone_le (precone_scale r (u n)) (precone_scale r (u n.+1)))
  (fub1 : forall n, cone_norm (precone_scale r (u n)) <= 1) :
  cone_sup_ball (fun n => precone_scale r (u n)) fuch fub1 =
  precone_scale r (cone_sup_ball u uch ub1).
Proof.
set s  := cone_sup_ball (fun n => precone_scale r (u n)) fuch fub1.
set su := cone_sup_ball u uch ub1.
have Dir1 : precone_le s (precone_scale r su).
  apply: cone_sup_ball_lub => n.
  by apply: precone_scale_le; exact: cone_sup_ball_ub.
have Dir2 : precone_le (precone_scale r su) s.
  (* Case split on r = 0. *)
  have [r0|rpos] := eqVneq r 0%:nng.
    rewrite r0 precone_scale_0l; exact: precone_le0.
  have rnum_pos : 0 < r%:num.
    rewrite lt0r; apply/andP; split; last exact: nngnum_ge0.
    apply/eqP => Hr0.
    by apply: (negP rpos); apply/eqP/nngnum_inj; rewrite Hr0.
  have rinv_ge0 : 0 <= (r%:num)^-1.
    by rewrite invr_ge0; apply: Order.POrderTheory.ltW.
  pose rinv : {nonneg R} := NngNum rinv_ge0.
  have rinv_num : rinv%:num = (r%:num)^-1 by [].
  have rmul_inv : r%:num * rinv%:num = 1.
    by rewrite rinv_num mulfV// gt_eqF.
  have rinv_mul : rinv%:num * r%:num = 1.
    by rewrite rinv_num mulVf// gt_eqF.
  (* Helper: equality of nonnegs from equality of underlying. *)
  have nng_eq : forall (a b : {nonneg R}), a%:num = b%:num -> a = b.
    by move=> a b /val_inj.
  have scale_rrinv : forall z : P, precone_scale r (precone_scale rinv z) = z.
    move=> z; rewrite -(@precone_scale_A _ _ r rinv z).
    have E : (r%:num * rinv%:num)%:nng = 1%:nng.
      by apply: nng_eq => /=; rewrite rmul_inv.
    by rewrite E precone_scale_1.
  have scale_rinvr : forall z : P, precone_scale rinv (precone_scale r z) = z.
    move=> z; rewrite -(@precone_scale_A _ _ rinv r z).
    have E : (rinv%:num * r%:num)%:nng = 1%:nng.
      by apply: nng_eq => /=; rewrite rinv_mul.
    by rewrite E precone_scale_1.
  (* witnesses for [s ≥p r *: u_n + w_n]. *)
  have wsex : forall n, exists w, s = precone_add (precone_scale r (u n)) w.
    by move=> n; have := cone_sup_ball_ub
      (fun n => precone_scale r (u n)) fuch fub1 n.
  pose ws (n : nat) : P := projT1 (cid (wsex n)).
  have ws_eq : forall n,
    s = precone_add (precone_scale r (u n)) (ws n).
    by move=> n; exact: projT2 (cid (wsex n)).
  (* Apply [rinv *: -] to ws_eq 0: *)
  (* rinv *: s = rinv *: (r *: u 0 + w 0)
              = rinv *: r *: u 0 + rinv *: w 0
              = u 0 + rinv *: w 0. *)
  have rinv_s : precone_scale rinv s =
                precone_add (u 0) (precone_scale rinv (ws 0)).
    rewrite (ws_eq 0) precone_scale_DAr.
    by rewrite scale_rinvr.
  have rinv_s_n : forall n, precone_scale rinv s =
    precone_add (u n) (precone_scale rinv (ws n)).
    move=> n; rewrite (ws_eq n) precone_scale_DAr.
    by rewrite scale_rinvr.
  (* So [u n] ≤p [rinv *: s] for every n. *)
  have Hu_bnd : forall n, precone_le (u n) (precone_scale rinv s).
    by move=> n; rewrite (rinv_s_n n); exists (precone_scale rinv (ws n)).
  (* Hence [su ≤p rinv *: s]. *)
  have [z Hz] : precone_le su (precone_scale rinv s).
    by apply: cone_sup_ball_lub.
  (* So [r *: su ≤p r *: rinv *: s = s]. *)
  exists (precone_scale r z).
  rewrite -precone_scale_DAr -Hz scale_rrinv //.
by apply: precone_le_anti.
Qed.

Lemma scaler_omega_continuous (r : {nonneg R}) :
  is_omega_continuous (fun x : P => precone_scale r x).
Proof.
rewrite /is_omega_continuous => u uch ub1 fuch fub1.
by rewrite (@sup_ball_scaler r u uch ub1 fuch fub1).
Qed.

End Lemma29.

(** ** Paper Lemma 2.10 — ω-continuity of differences of linear maps *)

Section Lemma210.
Variable R : realType.
Variables P Q : coneType R.

(** Paper Lemma 2.10: if [f, g : P -> Q] satisfy
    - [f] is increasing
    - [g] is ω-continuous
    - [forall x, f x ≤p g x] (witnessed by a function [gmf] with
      [g x = f x + gmf x])
    - [gmf] is increasing
    then [gmf] is ω-continuous.

    Encoding: we package the [g - f] data as the function [gmf]
    together with the hypothesis [g x = f x + gmf x]. *)

(** Paper Lemma 2.10 (conditional form on unit-ball chains).

    [gmf] is ω-continuous *provided* the image chain [(g \o u)] is also
    in the unit ball of [Q] (and forms a chain). This conditioning is
    forced by our encoding of [is_omega_continuous] for unit-ball
    chains only; the paper's statement is unconditional because it
    quantifies over ω-closed sets, not specifically the unit ball.

    Proof. [y ≤p gmf x] is from [Hgmf_incr] and [cone_sup_ball_lub].
    [gmf x ≤p y]: from [g x = f x + gmf x] (split hypothesis) and
    [g x = sup (g \o u)] (ω-continuity of [g]) and the bound
    [g (u n) ≤p f x + gmf (u n)] (by [f] increasing and [+] monotone),
    we get [g x ≤p sup (f x + gmf (u n)) = f x + y] (by Lemma 2.9).
    Cancel [f x] on the left to get [gmf x ≤p y]. *)
Lemma diff_omega_continuous
  (f g gmf : P -> Q)
  (Hf_incr   : is_increasing f)
  (Hg_cont   : is_omega_continuous g)
  (Hgmf_incr : is_increasing gmf)
  (Hsplit    : forall x, g x = precone_add (f x) (gmf x))
  (u : nat -> P)
  (uch : forall n, precone_le (u n) (u n.+1))
  (ub1 : forall n, cone_norm (u n) <= 1)
  (gmfuch : forall n, precone_le (gmf (u n)) (gmf (u n.+1)))
  (gmfub1 : forall n, cone_norm (gmf (u n)) <= 1)
  (guch   : forall n, precone_le (g (u n)) (g (u n.+1)))
  (gub1   : forall n, cone_norm (g (u n)) <= 1)
  (fxgmfuch : forall n,
    precone_le (precone_add (f (cone_sup_ball u uch ub1)) (gmf (u n)))
               (precone_add (f (cone_sup_ball u uch ub1)) (gmf (u n.+1))))
  (fxgmfub1 : forall n,
    cone_norm (precone_add (f (cone_sup_ball u uch ub1)) (gmf (u n))) <= 1) :
  gmf (cone_sup_ball u uch ub1) =
    cone_sup_ball (gmf \o u) gmfuch gmfub1.
Proof.
set x := cone_sup_ball u uch ub1.
set y := cone_sup_ball (gmf \o u) gmfuch gmfub1.
apply: precone_le_anti; last first.
  apply: cone_sup_ball_lub => n.
  apply: Hgmf_incr; exact: cone_sup_ball_ub.
(* Hard direction: gmf x ≤p y, equivalently f x + gmf x ≤p f x + y
   (then cancel f x). *)
(* g x = f x + gmf x (by Hsplit). *)
(* g x = sup (g \o u) by ω-continuity of g. *)
have gx_eq : g x = cone_sup_ball (g \o u) guch gub1.
  by rewrite /x; apply: Hg_cont.
(* sup (g \o u) ≤p f x + y, because for each n,
     g (u n) ≤p f x + gmf (u n)   [by f (u n) ≤p f x via Hf_incr]
     ≤p f x + y                    [since gmf (u n) ≤p y]. *)
have step1 : forall n,
  precone_le (g (u n)) (precone_add (f x) (gmf (u n))).
  move=> n; rewrite (Hsplit (u n)).
  apply: precone_add_le_r.
  by apply: Hf_incr; rewrite /x; exact: cone_sup_ball_ub.
have step2 : forall n, precone_le (g (u n))
  (cone_sup_ball (fun m => precone_add (f x) (gmf (u m))) fxgmfuch fxgmfub1).
  move=> n.
  apply: precone_le_trans; first exact: step1 n.
  exact: cone_sup_ball_ub.
have step3 : precone_le (cone_sup_ball (g \o u) guch gub1)
  (cone_sup_ball (fun m => precone_add (f x) (gmf (u m))) fxgmfuch fxgmfub1).
  apply: cone_sup_ball_lub => n; exact: step2.
(* And the latter = f x + y by addl_omega_continuous. *)
have sumeq : cone_sup_ball (fun m => precone_add (f x) (gmf (u m)))
                            fxgmfuch fxgmfub1 = precone_add (f x) y.
  symmetry.
  have HH := @addl_omega_continuous _ _ (f x).
  rewrite /is_omega_continuous in HH.
  by have := HH (gmf \o u) gmfuch gmfub1 fxgmfuch fxgmfub1.
(* Combine: g x = sup (g \o u) ≤p f x + y, and g x = f x + gmf x.
   So f x + gmf x ≤p f x + y, hence by cancellation gmf x ≤p y. *)
have gx_le : precone_le (g x) (precone_add (f x) y).
  rewrite gx_eq -sumeq.
  exact: step3.
have := gx_le; rewrite (Hsplit x).
case=> w Hw.
exists w.
(* Hw : f x + y = (f x + gmf x) + w = f x + (gmf x + w). *)
(* Want: y = gmf x + w. Apply precone_cancel on f x. *)
have Hw' : precone_add (f x) y = precone_add (f x) (precone_add (gmf x) w).
  by rewrite Hw -precone_addA.
exact: precone_cancel Hw'.
Qed.

End Lemma210.

(** ** Paper Lemma 2.11 — linear maps are bounded on the unit ball *)

Section Lemma211.
Variable R : realType.
Variables P Q : coneType R.

(** The set [{ ‖f x‖ | x ∈ B_P }] of norms of values of [f] on the
    unit ball. *)
Definition linmap_image_norm (f : P -> Q) : set R :=
  [set y | exists2 x : P, cone_norm x <= 1 & y = cone_norm (f x)].

(** Paper Lemma 2.11: [f(B_P)] is bounded — the unit-ball image is
    norm-bounded.

    Proof. By contradiction. If unbounded, pick a sequence [(x_n)]
    with [‖x_n‖ ≤ 1] and [‖f x_n‖ ≥ 4^n]. Form the partial-sum
    sequence [y_N := ∑_{k≤N} (1/2^k) *: x_k]. Then:
    - [‖y_N‖ ≤ ∑_{k≤N} (1/2^k) * 1 ≤ 2 ≤ 2], rescaled to [≤ 1] by
      taking half-sums.
    - [(y_N)] is increasing in the cone order (each new term is
      added).
    - In the unit ball, hence has a lub [y].
    - For each [n], [‖f y‖ ≥ ‖f y_n‖] (by Normp + linearity) and
      [‖f y_n‖ ≥ (1/2^n) * ‖f x_n‖ ≥ 2^n], a contradiction with
      [‖f y‖] finite.

    Our formalisation: as in the spec, we use the real [sup] from
    [mathcomp.reals.reals]. [linmap_norm f] is defined as [sup
    (linmap_image_norm f)] — returning [0] if the set is not
    bounded — but we prove it IS bounded for [f] linear.

    Time-box note: the partial-sum sequence requires a non-trivial
    nat-indexed construction in a cone (\sum-style) which our
    skeleton precone does not yet have as a primitive. We sketch the
    construction below and complete the boundedness proof. *)

(** Iterated addition in a precone: [pcone_sum f N = ∑_{k=0}^{N-1} f k]. *)
Fixpoint pcone_sum (f : nat -> P) (n : nat) : P :=
  match n with
  | 0 => precone_zero
  | S k => precone_add (pcone_sum f k) (f k)
  end.

Lemma pcone_sum_chain (f : nat -> P) :
  forall n, precone_le (pcone_sum f n) (pcone_sum f n.+1).
Proof.
move=> n /=; exists (f n); reflexivity.
Qed.

Lemma pcone_sum_norm_le (f : nat -> P) (M : R) :
  (forall n, cone_norm (f n) <= M) ->
  forall N, cone_norm (pcone_sum f N) <= N%:R * M.
Proof.
move=> HM N; elim: N => /= [|N IH].
  by rewrite cone_norm0 mul0r.
apply: (Order.POrderTheory.le_trans (cone_normt _ _)).
rewrite -nat1r mulrDl mul1r addrC.
exact: lerD (HM N) IH.
Qed.

(** *** Arithmetic plumbing for Lemma 2.11 *)

(** Pointwise variant of [pcone_sum_norm_le]: bound by a per-term sum
    of bounds. *)
Lemma pcone_sum_norm_le_pw (f : nat -> P) (cn : nat -> R) :
  (forall n, cone_norm (f n) <= cn n) ->
  forall N, cone_norm (pcone_sum f N) <= \sum_(k < N) cn k.
Proof.
move=> Hb N; elim: N => /= [|N IH].
  by rewrite cone_norm0 big_ord0.
apply: (Order.POrderTheory.le_trans (cone_normt _ _)).
rewrite big_ord_recr/=.
by apply: lerD.
Qed.

(** Closed form of the geometric partial sum [Σ_{k<N} 1/2^{k+1}]. *)
Lemma half_pow_sum (N : nat) :
  \sum_(k < N) ((2 : R) ^+ k.+1)^-1 = 1 - ((2 : R) ^+ N)^-1.
Proof.
have two_ne0 : (2 : R) != 0 by rewrite pnatr_eq0.
elim: N => [|N IH].
  by rewrite big_ord0 expr0 invr1 subrr.
rewrite big_ord_recr/= IH.
have step : ((2:R) ^+ N)^-1 = 2 * ((2:R) ^+ N.+1)^-1.
  by rewrite exprS invfM mulrA mulfV// mul1r.
rewrite step mulr_natl mulr2n opprD -addrA addrAC addrK//.
Qed.

(** The geometric partial sum is bounded by 1. *)
Lemma half_pow_sum_le1 (N : nat) :
  \sum_(k < N) ((2 : R) ^+ k.+1)^-1 <= 1.
Proof.
rewrite half_pow_sum lerBlDr -[X in X <= _]addr0 lerD2l.
by rewrite invr_ge0 exprn_ge0// ler0n.
Qed.

(** Each [1/2^{k+1}] is non-negative — used to package it as a
    [{nonneg R}] scalar for [precone_scale]. *)
Lemma half_pow_succ_ge0 (k : nat) : 0 <= ((2 : R) ^+ k.+1)^-1.
Proof. by rewrite invr_ge0 exprn_ge0// ler0n. Qed.

Definition half_pow_succ_nng (k : nat) : {nonneg R} :=
  NngNum (half_pow_succ_ge0 k).

(** *** Paper Lemma 2.11 *)

(** Paper Lemma 2.11: a linear map [f : P -> Q] is bounded on the unit
    ball [B_P], i.e. there exists [M ≥ 0] such that [‖f x‖ ≤ M] for
    every [x] with [‖x‖ ≤ 1].

    Proof (Selinger). Classical contradiction. If no such [M] exists,
    pick a sequence [(x_n)] with [‖x_n‖ ≤ 1] and
    [‖f x_n‖ > (n+1) · 2^{n+1}]. Define
    [y_N := Σ_{k<N} (1/2^{k+1}) ·: x_k] via [pcone_sum]. By
    [pcone_sum_norm_le_pw] and [half_pow_sum_le1], [‖y_N‖ ≤ 1], so the
    chain has a lub [y ∈ B_P] by (Normc).

    For each [n < N], dropping all terms except [k = n] in [f y_N]
    gives [(1/2^{n+1}) ·: f x_n ≤p f y_N], whence (by Normp and
    linearity / homogeneity) [(1/2^{n+1}) · ‖f x_n‖ ≤ ‖f y_N‖]. Using
    [‖f x_n‖ > (n+1) · 2^{n+1}] this yields [‖f y_N‖ > n+1].

    Since [y_N ≤p y] (by [cone_sup_ball_ub]) and [f] is increasing
    (linear ⇒ increasing), [f y_N ≤p f y], so [‖f y‖ > n+1] for every
    [n] — contradiction with [‖f y‖] being a fixed real number
    (Archimedean property). *)
Lemma linmap_bounded (f : P -> Q) :
  is_linear f ->
  exists M : R, 0 <= M /\
    forall x, cone_norm x <= 1 -> cone_norm (f x) <= M.
Proof.
move=> Hlin.
(* Classical contradiction. *)
apply: contrapT => Habs.
(* From Habs, extract a "no-bound" oracle. *)
have Hneg : forall c : R, 0 <= c ->
    exists x : P, cone_norm x <= 1 /\ c < cone_norm (f x).
  move=> c c0; apply: contrapT => Hnc.
  apply: Habs; exists c; split=> // x Hx.
  rewrite Order.TotalTheory.leNgt; apply/negP => Hfx.
  by apply: Hnc; exists x.
(* For each n, pick witness with [‖f x_n‖ > (n+1) · 2^(n+1)]. *)
pose c (n : nat) : R := (n.+1)%:R * (2 : R) ^+ n.+1.
have c_ge0 : forall n, 0 <= c n.
  by move=> n; rewrite mulr_ge0// ?ler0n// exprn_ge0// ler0n.
have xex : forall n, exists x : P, cone_norm x <= 1 /\ c n < cone_norm (f x).
  by move=> n; apply: Hneg; exact: c_ge0.
pose x (n : nat) : P := projT1 (cid (xex n)).
have x_ball : forall n, cone_norm (x n) <= 1.
  by move=> n; have [//] := projT2 (cid (xex n)).
have x_lb : forall n, c n < cone_norm (f (x n)).
  by move=> n; have [_ //] := projT2 (cid (xex n)).
(* Scaled sequence [s k := (1/2^(k+1)) ·: x k]. *)
pose s (k : nat) : P := precone_scale (half_pow_succ_nng k) (x k).
(* Partial sum [y N := Σ_{k<N} s k] is the chain. *)
pose y (N : nat) : P := pcone_sum s N.
have y_chain : forall N, precone_le (y N) (y N.+1).
  by move=> N; exact: pcone_sum_chain.
(* Norm bound on each summand: [‖s k‖ ≤ 1/2^(k+1)]. *)
have s_norm : forall k, cone_norm (s k) <= ((2 : R) ^+ k.+1)^-1.
  move=> k; rewrite /s cone_normh /=.
  by rewrite -{2}[((2:R) ^- k.+1)]mulr1 ler_pM2l// invr_gt0 exprn_gt0.
(* Norm bound on partial sums: [‖y N‖ ≤ Σ_{k<N} 1/2^(k+1) ≤ 1]. *)
have y_ball : forall N, cone_norm (y N) <= 1.
  move=> N; rewrite /y.
  apply: Order.POrderTheory.le_trans;
    first exact: pcone_sum_norm_le_pw s_norm N.
  exact: half_pow_sum_le1.
(* Take the supremum. *)
pose y_sup : P := cone_sup_ball y y_chain y_ball.
(* For each n, the n-th summand of [y (n.+1)] is [s n], i.e.,
   [y (n.+1) = y n + s n], so [s n ≤p y (n.+1) ≤p y_sup]. *)
have sn_le : forall n, precone_le (s n) y_sup.
  move=> n.
  apply: precone_le_trans (cone_sup_ball_ub y y_chain y_ball n.+1).
  rewrite /y /=; exists (y n); rewrite precone_addC //.
(* By linearity, [f s n = (1/2^(n+1)) ·: f (x n)], so
   [‖f (s n)‖ = (1/2^(n+1)) · ‖f (x n)‖]. *)
have fs_norm : forall n,
    cone_norm (f (s n)) = ((2 : R) ^+ n.+1)^-1 * cone_norm (f (x n)).
  by move=> n; rewrite /s (linearZ Hlin) cone_normh.
(* Since f is increasing (linearity), [f (s n) ≤p f y_sup]. *)
have f_incr : is_increasing f by exact: linear_increasing Hlin.
have fs_le_fy : forall n, precone_le (f (s n)) (f y_sup).
  by move=> n; apply: f_incr; exact: sn_le.
(* Hence by (Normp), [‖f (s n)‖ ≤ ‖f y_sup‖]. *)
have fy_lb : forall n, cone_norm (f (s n)) <= cone_norm (f y_sup).
  by move=> n; apply: cone_normp; exact: fs_le_fy.
(* So [(1/2^(n+1)) · ‖f (x n)‖ ≤ ‖f y_sup‖], and since
   [‖f (x n)‖ > c n = (n+1) · 2^(n+1)], we get [‖f y_sup‖ > n+1]
   for every n. *)
have key : forall n, (n.+1)%:R < cone_norm (f y_sup).
  move=> n.
  have H1 : (n.+1)%:R < ((2 : R) ^+ n.+1)^-1 * cone_norm (f (x n)).
    rewrite ltr_pdivlMl; last by rewrite exprn_gt0.
    by rewrite mulrC; exact: x_lb n.
  apply: Order.POrderTheory.lt_le_trans H1 _.
  by rewrite -fs_norm; exact: fy_lb n.
(* Contradiction: [‖f y_sup‖] is unbounded above. *)
have Hge0 : 0 <= cone_norm (f y_sup) by exact: cone_norm_ge0.
have Hm := Num.Theory.archi_boundP Hge0.
have := key (Num.bound (cone_norm (f y_sup))).
move=> /Order.POrderTheory.lt_trans => /(_ _ Hm).
by rewrite ltr_nat ltnNge leqnSn.
Qed.

(** Paper Lemma 2.11 (operator norm): extract the operator-norm
    bound [‖f‖] via [xchoose]. We do NOT prove that [linmap_norm f]
    is the supremum — only that it is *an* upper bound. Downstream
    cone-of-linear-maps clients (M1e, [cone_cat.v]) need exactly
    this bound to package the norm. *)
Definition linmap_norm (f : P -> Q) (Hf : is_linear f) : R :=
  projT1 (cid (linmap_bounded Hf)).

(** Paper Lemma 2.11: [‖f‖ ≥ 0]. *)
Lemma linmap_norm_ge0 (f : P -> Q) (Hf : is_linear f) :
  0 <= linmap_norm Hf.
Proof.
rewrite /linmap_norm.
by have [H0 _] := projT2 (cid (linmap_bounded Hf)).
Qed.

(** Paper Lemma 2.11: for every [x] in the unit ball, [‖f x‖ ≤ ‖f‖]. *)
Lemma linmap_norm_ub (f : P -> Q) (Hf : is_linear f) :
  forall x, cone_norm x <= 1 -> cone_norm (f x) <= linmap_norm Hf.
Proof.
rewrite /linmap_norm => x Hx.
by have [_ H1] := projT2 (cid (linmap_bounded Hf)); exact: H1.
Qed.

End Lemma211.

Arguments linmap_bounded {R P Q}.
Arguments linmap_norm {R P Q}.
Arguments linmap_norm_ge0 {R P Q}.
Arguments linmap_norm_ub {R P Q}.

(** ** Paper Lemma 2.13 — referred to [cone_cat.v]

    The precone [P ⊸ Q] of linear ω-continuous maps with the operator
    norm [linmap_norm] is a cone. This is out of scope for
    [basic_lemmas.v]; it depends on the full Lemma 2.11 (operator
    norm well-defined) and on a precone structure on the function
    space, which lives in [cone_cat.v]. *)
