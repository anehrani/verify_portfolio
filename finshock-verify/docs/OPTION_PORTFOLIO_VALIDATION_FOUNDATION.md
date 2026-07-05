# Option Portfolio Validation Foundation

This project should evolve into a validation system for option hedged
portfolios, with crypto option hedges as the first target market.

## Core Principle

The system should not claim that a portfolio is safe in every real-world sense.
It should prove conditional statements:

> If the option contract is valid, settles according to the stated payoff, and
> the hedge coverage assumptions hold, then the terminal wealth floor follows
> for every modeled final spot price.

That is the right shape for model validation and regulatory review.

## Formal Layers

1. `Options/Vanilla.v`
   - vanilla call and put payoff definitions;
   - option leg and option book aggregation;
   - nonnegativity theorems for long option payoffs.

2. `Options/PortfolioValidation.v`
   - spot plus put hedge value;
   - hedge coverage predicate;
   - terminal wealth floor definition;
   - covered protective-put floor theorem.

3. `Options/CryptoProtectivePut.v`
   - crypto-specific wrapper around the generic validation layer;
   - matching long-crypto plus long-put theorem;
   - checked harsh-drop example.

## Current Main Theorem

The generic validation theorem is:

```coq
Theorem covered_protective_put_wealth_floor :
  forall cash premium spot_units put_units final_spot strike,
    0 <= spot_units ->
    spot_units <= put_units ->
    terminal_wealth_floor cash premium spot_units strike
    <= covered_protective_put_wealth
         cash premium spot_units put_units final_spot strike.
```

In plain English:

> If long put units cover the long spot units, then terminal wealth is at least
> cash minus premium plus spot units times strike, for every final spot price.

## Validation Workflow

1. Normalize the option book:
   - underlying asset;
   - option kind;
   - strike;
   - maturity;
   - quantity;
   - premium;
   - settlement style.

2. Normalize the spot book:
   - spot units;
   - cash;
   - custody venue;
   - valuation currency.

3. Check hedge coverage:
   - spot units are nonnegative;
   - long put units are greater than or equal to spot units;
   - maturity and underlying match;
   - strike is the intended risk floor.

4. Run harsh-drop scenarios:
   - final spot equal to zero;
   - 30%, 50%, 80%, 95% crashes;
   - exchange/index disruption scenarios;
   - liquidity and collateral scenarios.

5. Produce audit output:
   - exact input values;
   - computed terminal wealth;
   - formal theorem used;
   - assumptions that are outside the proof.

## Assumptions Outside The Current Proof

- legal enforceability;
- venue registration or exemption;
- counterparty or clearing solvency;
- custody and wallet safety;
- oracle/index integrity;
- margin and liquidation mechanics;
- settlement failures;
- taxes, funding, and operational fees beyond explicit premium/cash inputs.

These assumptions should be recorded in validation reports rather than hidden.

## Next Proof Obligations

1. Collars: long spot + long put + short call.
2. Put spreads: long put at high strike + short put at low strike.
3. Multi-strike option books.
4. Maturity matching and roll validation.
5. Cash-settled versus physically settled options.
6. Margin and liquidation state transitions.
7. Finite expected shortfall over crypto crash scenarios.
