(**
  Single public entry point for FinanceVerify.

  Usage:
    From FinanceVerify Require Import All.
*)

From FinanceVerify Require Export Interfaces.
From FinanceVerify Require Export Core.
From FinanceVerify Require Export Risk.
From FinanceVerify Require Export Derivatives.
From FinanceVerify Require Export Pricing.
From FinanceVerify Require Export Exchange.
From FinanceVerify Require Export Examples.

(** Short, stable names for the main domains. *)
Module Accounting := Core.Accounting.
Module Stress := Risk.WeightedStress.
Module Options := Derivatives.
Module StatePricePricing := Pricing.StatePrices.
Module NoArbitrage := Pricing.NoArbitrage.
Module Matching := Exchange.Experimental.
