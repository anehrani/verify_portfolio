# Paper Sketch

## Working Title

Machine-Checked Verification of Portfolio Rebalancing under Discontinuous Price
Shocks

## Abstract Sketch

Portfolio-risk systems often combine market shocks, rebalancing rules,
transaction costs, and mandate constraints. Implementation errors in these
state transitions can create incorrect exposure, leverage, or solvency reports.
We present FinShockVerify, a Rocq-based framework for mechanically verifying
portfolio accounting and finite stress-scenario invariants under discontinuous
price jumps. The first library formalizes cash, risky holdings, price jumps,
self-financing trades with fees, weighted stress scenarios, and long-only loss
floors using exact rational arithmetic. The framework produces both executable
checks and machine-checked proofs of core accounting and risk properties.

## Core Contributions

1. A formal transition semantics for portfolio value under price jumps.
2. A verified accounting model for trades with explicit fees.
3. A finite stress-scenario model using exact rational arithmetic.
4. A checked theorem connecting long-only fully invested portfolios with
   portfolio-level loss floors.
5. A prototype command-line checker for stress-scenario files.

## Evaluation Plan

- Case study 1: long-only equity/bond portfolio under finite stress shocks.
- Case study 2: leveraged portfolio with gross-leverage constraints.
- Case study 3: threshold rebalancing with transaction costs.
- Case study 4: option overlay represented by piecewise-linear payoff shocks.

## Positioning

The system does not forecast markets or certify investment performance. It
certifies that explicitly specified portfolio transitions and risk checks match
their mathematical definitions.
