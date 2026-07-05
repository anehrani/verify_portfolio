(**
  Assumption audit for the verified public core.

  Experimental exchange theorems are intentionally omitted here because the
  source prototype explicitly contains admitted declarations.
*)

From FinanceVerify Require Import Interfaces.
From FinanceVerify Require Import Core.
From FinanceVerify Require Import Risk.
From FinanceVerify Require Import Derivatives.
From FinanceVerify Require Import Pricing.

Print Assumptions run_preserves.
Print Assumptions Core.Accounting.trade_self_financing.
Print Assumptions Risk.WeightedStress.long_only_fully_invested_loss_floor.
Print Assumptions
  Derivatives.PortfolioValidation.hedge_covers_floor.
Print Assumptions
  Derivatives.CryptoProtectivePut.protected_crypto_wealth_floor.
Print Assumptions Pricing.StatePrices.statePricePricing_nonneg.
Print Assumptions
  Pricing.NoArbitrage.putCall_parity_from_no_arbitrage.
Print Assumptions
  Pricing.NoArbitrage.forward_price_eq_spot_div_discount.
