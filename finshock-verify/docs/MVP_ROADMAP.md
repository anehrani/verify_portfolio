# FinShockVerify MVP Roadmap

FinShockVerify is an open-source verification system for portfolio changes
under discontinuous price jumps. The MVP focuses on exact finite stress
scenarios, rational arithmetic, and machine-checked invariants.

## Version 0 Scope

- Model cash, holdings, price jumps, and one-asset trades.
- Prove self-financing trade accounting with explicit fees.
- Model finite weighted stress scenarios.
- Prove that long-only, fully invested portfolios cannot lose more than the
  worst individual asset-return floor.
- Provide a small exact-arithmetic CLI for scenario files.

## What This Proves

- Trades update cash and holdings consistently.
- Price jumps produce the expected mark-to-market PnL.
- Stress-scenario pass/fail checks match the formal inequality.
- A long-only fully invested portfolio has a portfolio loss floor when every
  asset has the same loss floor.

## What This Does Not Claim Yet

- It does not predict market prices.
- It does not prove a strategy is profitable.
- It does not model continuous-time stochastic processes.
- It does not yet verify floating-point implementation behavior.

## Next Technical Milestones

1. Multi-asset holdings and trade vectors.
2. Transaction-cost models for rebalancing rules.
3. Mandate constraints: long-only, max position, sector cap, leverage cap.
4. Finite probability distributions and expected shortfall over scenarios.
5. Rocq extraction to OCaml for a proof-connected executable checker.
6. Import/export adapters for CSV, portfolio-management systems, and ACTUS-like
   financial-contract data.
