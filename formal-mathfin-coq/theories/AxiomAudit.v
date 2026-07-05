(*
  SPDX-License-Identifier: Apache-2.0

  Assumption visibility for the first load-bearing ported theorems.
  `make audit` also re-checks this compiled module with Rocq's kernel checker.
*)

From MathFin.Foundations Require Import StatePrices.
From MathFin.Foundations Require Import NoArbitrageDerivations.

Print Assumptions statePricePricing_nonneg.
Print Assumptions putCall_parity_from_no_arbitrage.
Print Assumptions forward_price_eq_spot_div_discount.
