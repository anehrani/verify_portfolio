(**
  Validation-oriented theorems for option hedged portfolios.

  These theorems are intended to support safety cases such as:
  "Given valid option settlement and adequate coverage, this option hedge
  enforces a terminal downside floor under any spot-price drop."
*)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import micromega.Lqa.
From Stdlib Require Import setoid_ring.Ring.
From FinShockVerify.Options Require Import Vanilla.

Open Scope Q_scope.

Definition spot_value (units final_spot : Q) : Q :=
  units * final_spot.

Definition covered_protective_put_value
    (spot_units put_units final_spot strike : Q) : Q :=
  spot_value spot_units final_spot
  + put_units * put_payoff final_spot strike.

Definition covered_protective_put_wealth
    (cash premium spot_units put_units final_spot strike : Q) : Q :=
  cash - premium
  + covered_protective_put_value spot_units put_units final_spot strike.

Definition hedge_covers (spot_units put_units : Q) : Prop :=
  0 <= spot_units /\ spot_units <= put_units.

Definition terminal_wealth_floor
    (cash premium spot_units strike : Q) : Q :=
  cash - premium + spot_units * strike.

Theorem covered_protective_put_value_floor :
  forall spot_units put_units final_spot strike,
    0 <= spot_units ->
    spot_units <= put_units ->
    spot_units * strike
    <= covered_protective_put_value
         spot_units put_units final_spot strike.
Proof.
  intros spot_units put_units final_spot strike Hspot_nonneg Hcovered.
  unfold covered_protective_put_value, spot_value, put_payoff, positive_part.
  destruct (Qlt_le_dec 0 (strike - final_spot)) as [Hbelow|Habove].
  - assert (Hscaled :
      spot_units * (strike - final_spot)
      <= put_units * (strike - final_spot)).
    {
      apply Qmult_le_compat_r; [exact Hcovered | lra].
    }
    setoid_replace (spot_units * strike)
      with (spot_units * final_spot
            + spot_units * (strike - final_spot)) by ring.
    lra.
  - assert (Hstrike_le_spot : strike <= final_spot) by lra.
    setoid_replace (spot_units * strike) with (strike * spot_units) by ring.
    setoid_replace (spot_units * final_spot + put_units * 0)
      with (final_spot * spot_units) by ring.
    apply Qmult_le_compat_r; [exact Hstrike_le_spot | exact Hspot_nonneg].
Qed.

Theorem covered_protective_put_wealth_floor :
  forall cash premium spot_units put_units final_spot strike,
    0 <= spot_units ->
    spot_units <= put_units ->
    terminal_wealth_floor cash premium spot_units strike
    <= covered_protective_put_wealth
         cash premium spot_units put_units final_spot strike.
Proof.
  intros cash premium spot_units put_units final_spot strike
    Hspot_nonneg Hcovered.
  unfold terminal_wealth_floor, covered_protective_put_wealth.
  pose proof
    (covered_protective_put_value_floor
      spot_units put_units final_spot strike
      Hspot_nonneg Hcovered) as Hfloor.
  lra.
Qed.

Theorem matching_protective_put_wealth_floor :
  forall cash premium units final_spot strike,
    0 <= units ->
    terminal_wealth_floor cash premium units strike
    <= covered_protective_put_wealth
         cash premium units units final_spot strike.
Proof.
  intros cash premium units final_spot strike Hunits.
  apply covered_protective_put_wealth_floor.
  - exact Hunits.
  - lra.
Qed.

Theorem hedge_covers_floor :
  forall cash premium spot_units put_units final_spot strike,
    hedge_covers spot_units put_units ->
    terminal_wealth_floor cash premium spot_units strike
    <= covered_protective_put_wealth
         cash premium spot_units put_units final_spot strike.
Proof.
  intros cash premium spot_units put_units final_spot strike Hcovers.
  destruct Hcovers as [Hspot_nonneg Hcovered].
  apply covered_protective_put_wealth_floor; assumption.
Qed.

Example one_btc_overhedged_put_crash_floor :
  terminal_wealth_floor 0 5000 1 80000
  <= covered_protective_put_wealth 0 5000 1 (3 # 2) 30000 80000.
Proof.
  apply covered_protective_put_wealth_floor.
  - discriminate.
  - discriminate.
Qed.
