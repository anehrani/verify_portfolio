(*
  SPDX-License-Identifier: Apache-2.0

  Rocq/Coq port of MathFin/Foundations/NoArbitrageDerivations.lean at upstream
  commit d7766e48e2f4761df26e0885bfeea14571d973c6.

  Original Lean development:
    Copyright (c) 2026 Raphael Coelho.

  This file contains translation and representation changes for Rocq.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lra.
From Stdlib Require Import setoid_ring.Ring.
From MathFin.Foundations Require Import StatePrices.

Import ListNotations.
Open Scope R_scope.

(** Positive-part payoff. *)
Definition positive_part (x : R) : R := Rmax x 0.

(** Finance-named form of max(x,0) - max(-x,0) = x. *)
Theorem max_sub_max_neg :
  forall x : R,
    positive_part x - positive_part (- x) = x.
Proof.
  intros x.
  unfold positive_part.
  destruct (Rle_dec 0 x) as [Hx | Hx].
  - rewrite Rmax_left by lra.
    rewrite Rmax_right by lra.
    lra.
  - assert (Hx' : x <= 0) by lra.
    rewrite Rmax_right by lra.
    rewrite Rmax_left by lra.
    lra.
Qed.

Definition call_payoff (spot strike : R) : R :=
  positive_part (spot - strike).

Definition put_payoff (spot strike : R) : R :=
  positive_part (strike - spot).

Section NoArbitrage.

Context {I : Type}.

Lemma statePricePricing_spot_minus_const :
  forall (states : list I) (q S : I -> R) (K : R),
    statePricePricing states q (fun i => S i - K) =
    statePricePricing states q S - K * finite_sum states q.
Proof.
  intros states q S K.
  unfold statePricePricing.
  induction states as [| i rest IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** Put-call parity derived only from a finite-state linear pricing rule. *)
Theorem putCall_parity_from_no_arbitrage :
  forall (states : list I) (q S : I -> R) (DF S0 K : R),
    finite_sum states q = DF ->
    statePricePricing states q S = S0 ->
    statePricePricing states q (fun i => call_payoff (S i) K) -
    statePricePricing states q (fun i => put_payoff (S i) K) =
    S0 - K * DF.
Proof.
  intros states q S DF S0 K Hbond Hstock.
  rewrite <- statePricePricing_sub.
  transitivity
    (statePricePricing states q (fun i => S i - K)).
  - apply statePricePricing_ext.
    intros i Hi.
    unfold call_payoff, put_payoff.
    replace (K - S i) with (- (S i - K)) by ring.
    apply max_sub_max_neg.
  - rewrite statePricePricing_spot_minus_const.
    rewrite Hbond, Hstock.
    reflexivity.
Qed.

(** The fair forward strike is spot divided by the discount factor. *)
Theorem forward_price_from_no_arbitrage :
  forall (states : list I) (q S : I -> R) (DF S0 F : R),
    DF <> 0 ->
    finite_sum states q = DF ->
    statePricePricing states q S = S0 ->
    (statePricePricing states q (fun i => S i - F) = 0 <->
     F = S0 / DF).
Proof.
  intros states q S DF S0 F HDF Hbond Hstock.
  rewrite statePricePricing_spot_minus_const.
  rewrite Hbond, Hstock.
  split; intro H.
  - apply (Rmult_eq_reg_r DF).
    2: exact HDF.
    unfold Rdiv.
    rewrite Rmult_assoc.
    rewrite (Rinv_l DF HDF).
    lra.
  - rewrite H.
    unfold Rdiv.
    rewrite Rmult_assoc.
    rewrite (Rinv_l DF HDF).
    ring.
Qed.

(** The fair forward strike exists and is unique. *)
Theorem forward_price_eq_spot_div_discount :
  forall (states : list I) (q S : I -> R) (DF S0 : R),
    DF <> 0 ->
    finite_sum states q = DF ->
    statePricePricing states q S = S0 ->
    exists! F : R,
      statePricePricing states q (fun i => S i - F) = 0.
Proof.
  intros states q S DF S0 HDF Hbond Hstock.
  exists (S0 / DF).
  split.
  - apply (proj2
      (forward_price_from_no_arbitrage
        states q S DF S0 (S0 / DF) HDF Hbond Hstock)).
    reflexivity.
  - intros F HF.
    symmetry.
    apply (proj1
      (forward_price_from_no_arbitrage
        states q S DF S0 F HDF Hbond Hstock)).
    exact HF.
Qed.

End NoArbitrage.
