(**
  Protective-put floor for a crypto option hedged portfolio.

  This module models the payoff layer only. The theorem assumes that the put
  option is valid, enforceable, and settles according to its payoff definition.
  It does not model counterparty default, exchange failure, custody loss,
  oracle/index manipulation, or legal eligibility.
*)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import micromega.Lqa.
From Stdlib Require Import setoid_ring.Ring.
From FinShockVerify.Options Require Import Vanilla.
From FinShockVerify.Options Require Import PortfolioValidation.

Open Scope Q_scope.

Definition long_put_payoff (final_spot strike : Q) : Q :=
  put_payoff final_spot strike.

Definition crypto_spot_value (units final_spot : Q) : Q :=
  units * final_spot.

Definition protected_crypto_value
    (units final_spot strike : Q) : Q :=
  units * (final_spot + long_put_payoff final_spot strike).

Definition protected_crypto_wealth
    (cash premium units final_spot strike : Q) : Q :=
  cash - premium + protected_crypto_value units final_spot strike.

Theorem positive_part_nonnegative :
  forall x,
    0 <= positive_part x.
Proof.
  apply Vanilla.positive_part_nonnegative.
Qed.

Theorem spot_plus_put_strike_floor :
  forall final_spot strike,
    strike <= final_spot + long_put_payoff final_spot strike.
Proof.
  intros final_spot strike.
  unfold long_put_payoff, put_payoff, positive_part.
  destruct (Qlt_le_dec 0 (strike - final_spot)) as [Hpos|Hnonpos].
  - lra.
  - lra.
Qed.

Theorem protected_crypto_value_floor :
  forall units final_spot strike,
    0 <= units ->
    units * strike <= protected_crypto_value units final_spot strike.
Proof.
  intros units final_spot strike Hunits.
  unfold protected_crypto_value.
  setoid_replace (units * strike) with (strike * units) by ring.
  setoid_replace (units * (final_spot + long_put_payoff final_spot strike))
    with ((final_spot + long_put_payoff final_spot strike) * units) by ring.
  apply Qmult_le_compat_r.
  - apply spot_plus_put_strike_floor.
  - exact Hunits.
Qed.

Theorem protected_crypto_wealth_floor :
  forall cash premium units final_spot strike,
    0 <= units ->
    cash - premium + units * strike
    <= protected_crypto_wealth cash premium units final_spot strike.
Proof.
  intros cash premium units final_spot strike Hunits.
  setoid_replace (protected_crypto_wealth cash premium units final_spot strike)
    with (covered_protective_put_wealth
      cash premium units units final_spot strike).
  2:{
    unfold protected_crypto_wealth, protected_crypto_value, long_put_payoff.
    unfold covered_protective_put_wealth, covered_protective_put_value.
    unfold spot_value.
    ring.
  }
  change (terminal_wealth_floor cash premium units strike
    <= covered_protective_put_wealth cash premium units units final_spot strike).
  apply matching_protective_put_wealth_floor.
  exact Hunits.
Qed.

Theorem protected_crypto_dominates_spot :
  forall units final_spot strike,
    0 <= units ->
    crypto_spot_value units final_spot
    <= protected_crypto_value units final_spot strike.
Proof.
  intros units final_spot strike Hunits.
  unfold crypto_spot_value, protected_crypto_value.
  setoid_replace
    (units * (final_spot + long_put_payoff final_spot strike))
    with (units * final_spot + units * long_put_payoff final_spot strike)
    by ring.
  assert (Hput : 0 <= long_put_payoff final_spot strike).
  {
    unfold long_put_payoff.
    apply positive_part_nonnegative.
  }
  pose proof (Qmult_le_0_compat units (long_put_payoff final_spot strike)
    Hunits Hput) as Hoption_nonnegative.
  lra.
Qed.

Theorem protected_crypto_value_equals_floor_below_strike :
  forall units final_spot strike,
    final_spot <= strike ->
    protected_crypto_value units final_spot strike == units * strike.
Proof.
  intros units final_spot strike Hbelow.
  unfold protected_crypto_value, long_put_payoff, put_payoff, positive_part.
  destruct (Qlt_le_dec 0 (strike - final_spot)) as [Hpos|Hnonpos].
  - ring.
  - assert (Hspot_eq : final_spot == strike) by lra.
    setoid_rewrite Hspot_eq.
    ring.
Qed.

Example one_btc_put_crash_floor :
  0 - 5000 + 1 * 80000
  <= protected_crypto_wealth 0 5000 1 30000 80000.
Proof.
  apply protected_crypto_wealth_floor.
  discriminate.
Qed.
