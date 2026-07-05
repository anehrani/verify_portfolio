(*
  SPDX-License-Identifier: Apache-2.0

  Rocq/Coq port of MathFin/Foundations/StatePrices.lean at upstream commit
  d7766e48e2f4761df26e0885bfeea14571d973c6.

  Original Lean development:
    Copyright (c) 2026 Raphael Coelho.

  This file contains translation and representation changes for Rocq.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lra.
From Stdlib Require Import setoid_ring.Ring.

Import ListNotations.
Open Scope R_scope.

Section StatePrices.

Context {I : Type}.

(** A finite sum over an explicit enumeration of states. *)
Fixpoint finite_sum (states : list I) (f : I -> R) : R :=
  match states with
  | [] => 0
  | i :: rest => f i + finite_sum rest f
  end.

(** Linear pricing from Arrow-Debreu state prices:
    V_0(X) = sum_i q_i X_i. *)
Definition statePricePricing
    (states : list I) (q X : I -> R) : R :=
  finite_sum states (fun i => q i * X i).

Theorem finite_sum_ext :
  forall (states : list I) (f g : I -> R),
    (forall i, In i states -> f i = g i) ->
    finite_sum states f = finite_sum states g.
Proof.
  induction states as [| i rest IH]; intros f g Heq.
  - reflexivity.
  - simpl.
    rewrite (Heq i (or_introl eq_refl)).
    rewrite (IH f g).
    + reflexivity.
    + intros j Hj. apply Heq. right. exact Hj.
Qed.

Theorem finite_sum_add :
  forall (states : list I) (f g : I -> R),
    finite_sum states (fun i => f i + g i) =
    finite_sum states f + finite_sum states g.
Proof.
  induction states as [| i rest IH]; intros f g; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Theorem finite_sum_smul :
  forall (states : list I) (c : R) (f : I -> R),
    finite_sum states (fun i => c * f i) =
    c * finite_sum states f.
Proof.
  induction states as [| i rest IH]; intros c f; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** Zero payoff has zero price. *)
Theorem statePricePricing_zero :
  forall (states : list I) (q : I -> R),
    statePricePricing states q (fun _ => 0) = 0.
Proof.
  intros states q.
  unfold statePricePricing.
  induction states as [| i rest IH]; simpl.
  - reflexivity.
  - rewrite IH. ring.
Qed.

(** Unit-payoff price equals the sum of state prices. *)
Theorem statePricePricing_one :
  forall (states : list I) (q : I -> R),
    statePricePricing states q (fun _ => 1) =
    finite_sum states q.
Proof.
  intros states q.
  unfold statePricePricing.
  induction states as [| i rest IH]; simpl.
  - reflexivity.
  - rewrite IH. ring.
Qed.

(** A constant payoff is the constant times the unit-payoff price. *)
Theorem statePricePricing_const :
  forall (states : list I) (q : I -> R) (c : R),
    statePricePricing states q (fun _ => c) =
    c * finite_sum states q.
Proof.
  intros states q c.
  unfold statePricePricing.
  induction states as [| i rest IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** Linearity in the payoff: additivity. *)
Theorem statePricePricing_add :
  forall (states : list I) (q X Y : I -> R),
    statePricePricing states q (fun i => X i + Y i) =
    statePricePricing states q X + statePricePricing states q Y.
Proof.
  intros states q X Y.
  unfold statePricePricing.
  induction states as [| i rest IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** Linearity in the payoff: scalar homogeneity. *)
Theorem statePricePricing_smul :
  forall (states : list I) (q X : I -> R) (c : R),
    statePricePricing states q (fun i => c * X i) =
    c * statePricePricing states q X.
Proof.
  intros states q X c.
  unfold statePricePricing.
  induction states as [| i rest IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Theorem statePricePricing_sub :
  forall (states : list I) (q X Y : I -> R),
    statePricePricing states q (fun i => X i - Y i) =
    statePricePricing states q X - statePricePricing states q Y.
Proof.
  intros states q X Y.
  unfold statePricePricing.
  induction states as [| i rest IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Theorem statePricePricing_ext :
  forall (states : list I) (q X Y : I -> R),
    (forall i, In i states -> X i = Y i) ->
    statePricePricing states q X = statePricePricing states q Y.
Proof.
  intros states q X Y Heq.
  unfold statePricePricing.
  apply finite_sum_ext.
  intros i Hi.
  rewrite (Heq i Hi).
  reflexivity.
Qed.

(** Discounted risk-neutral expectation written as state prices. *)
Theorem statePricePricing_eq_riskNeutral :
  forall (states : list I) (nu X : I -> R) (rT : R),
    statePricePricing states (fun i => exp (- rT) * nu i) X =
    exp (- rT) * finite_sum states (fun i => nu i * X i).
Proof.
  intros states nu X rT.
  unfold statePricePricing.
  induction states as [| i rest IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** Non-negative state prices and payoffs give a non-negative price. *)
Theorem statePricePricing_nonneg :
  forall (states : list I) (q X : I -> R),
    (forall i, In i states -> 0 <= q i) ->
    (forall i, In i states -> 0 <= X i) ->
    0 <= statePricePricing states q X.
Proof.
  intros states.
  induction states as [| i rest IH]; intros q X Hq HX.
  - change (0 <= 0). lra.
  - change
      (0 <= q i * X i + statePricePricing rest q X).
    assert (Hqi : 0 <= q i) by (apply Hq; left; reflexivity).
    assert (HXi : 0 <= X i) by (apply HX; left; reflexivity).
    assert (Hhead : 0 <= q i * X i) by nra.
    assert (Htail : 0 <= statePricePricing rest q X).
    {
      apply IH.
      - intros j Hj. apply Hq. right. exact Hj.
      - intros j Hj. apply HX. right. exact Hj.
    }
    lra.
Qed.

End StatePrices.
