(**
  Reusable vanilla option payoff primitives for option portfolio validation.

  This module is deliberately payoff-level: it models terminal option payoffs
  over exact rational numbers. Premiums, margin, settlement, custody, and venue
  assumptions are handled by higher-level validation modules.
*)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lqa.
From Stdlib Require Import setoid_ring.Ring.

Import ListNotations.
Open Scope Q_scope.

Inductive OptionKind :=
| Call
| Put.

Definition positive_part (x : Q) : Q :=
  match Qlt_le_dec 0 x with
  | left _ => x
  | right _ => 0
  end.

Definition call_payoff (final_spot strike : Q) : Q :=
  positive_part (final_spot - strike).

Definition put_payoff (final_spot strike : Q) : Q :=
  positive_part (strike - final_spot).

Definition option_payoff
    (kind : OptionKind) (final_spot strike : Q) : Q :=
  match kind with
  | Call => call_payoff final_spot strike
  | Put => put_payoff final_spot strike
  end.

Record OptionLeg := {
  leg_kind : OptionKind;
  leg_quantity : Q;
  leg_strike : Q
}.

Definition option_leg_payoff (leg : OptionLeg) (final_spot : Q) : Q :=
  leg_quantity leg * option_payoff (leg_kind leg) final_spot (leg_strike leg).

Fixpoint option_book_payoff
    (legs : list OptionLeg) (final_spot : Q) : Q :=
  match legs with
  | [] => 0
  | leg :: rest => option_leg_payoff leg final_spot
                 + option_book_payoff rest final_spot
  end.

Theorem positive_part_nonnegative :
  forall x,
    0 <= positive_part x.
Proof.
  intros x.
  unfold positive_part.
  destruct (Qlt_le_dec 0 x); lra.
Qed.

Theorem call_payoff_nonnegative :
  forall final_spot strike,
    0 <= call_payoff final_spot strike.
Proof.
  intros final_spot strike.
  unfold call_payoff.
  apply positive_part_nonnegative.
Qed.

Theorem put_payoff_nonnegative :
  forall final_spot strike,
    0 <= put_payoff final_spot strike.
Proof.
  intros final_spot strike.
  unfold put_payoff.
  apply positive_part_nonnegative.
Qed.

Theorem option_payoff_nonnegative :
  forall kind final_spot strike,
    0 <= option_payoff kind final_spot strike.
Proof.
  intros kind final_spot strike.
  destruct kind.
  - apply call_payoff_nonnegative.
  - apply put_payoff_nonnegative.
Qed.

Theorem long_option_leg_payoff_nonnegative :
  forall leg final_spot,
    0 <= leg_quantity leg ->
    0 <= option_leg_payoff leg final_spot.
Proof.
  intros leg final_spot Hquantity.
  unfold option_leg_payoff.
  apply Qmult_le_0_compat.
  - exact Hquantity.
  - apply option_payoff_nonnegative.
Qed.

Theorem option_book_payoff_app :
  forall left right final_spot,
    option_book_payoff (left ++ right) final_spot
    == option_book_payoff left final_spot
     + option_book_payoff right final_spot.
Proof.
  induction left as [| leg rest IH]; intros right final_spot.
  - simpl.
    ring.
  - simpl.
    setoid_rewrite IH.
    ring.
Qed.
