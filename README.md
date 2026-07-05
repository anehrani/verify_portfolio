# FinanceVerify

FinanceVerify is the unified Rocq/Coq library in this repository. It combines
exact portfolio accounting, finite stress verification, option payoff and
hedge proofs, finite-state no-arbitrage pricing, and the option-exchange
prototype behind one build and one public namespace.

The library targets Rocq 9.1.1 and uses only the standard library.

## Build and audit

```sh
make build
make audit
```

`make build` compiles every Coq source in the repository, including the
compatibility entry point at `src/example.v`. `make audit` asks Rocq's kernel
checker to re-check `FinanceVerify.Audit`.

## Public API

Import the complete library with:

```coq
From FinanceVerify Require Import All.
```

The stable domain modules are:

| Module | Purpose | Numeric domain |
|---|---|---|
| `Accounting` | cash, shares, price transitions, and self-financing trades | `Q` |
| `Stress` | weighted scenarios, leverage, and executable loss-floor checks | `Q` |
| `Options.Vanilla` | vanilla payoffs, legs, and books | `Q` |
| `Options.PortfolioValidation` | hedge coverage and terminal wealth floors | `Q` |
| `Options.CryptoProtectivePut` | protective-put specialization | `Q` |
| `StatePricePricing` | finite Arrow-Debreu state-price valuation | `R` |
| `NoArbitrage` | put-call parity and fair-forward derivations | `R` |
| `Matching` | orders, continuous matching, auctions, and multi-leg strategies | `Z`, `nat` |

For example:

```coq
From FinanceVerify Require Import All.

Check Accounting.trade_self_financing.
Check Stress.long_only_fully_invested_loss_floor.
Check Options.PortfolioValidation.hedge_covers_floor.
Check NoArbitrage.putCall_parity_from_no_arbitrage.
```

## Architecture for extensions

`FinanceVerify.Interfaces` provides three small, numeric-domain-independent
building blocks:

- `SoundChecker` connects an executable Boolean checker to its proposition.
- `TransitionSystem`, `invariant`, and `run_preserves` support multi-event
  models such as order lifecycles, settlement, rebalancing, and margin calls.
- `ValuationModel` and `dominates` support richer positions and market states.

New code should be added as a focused module under `theories/`, then exported
from `theories/All.v`. Keep `Q` models for executable exact checks, `R` models
for analytic pricing statements, and make conversions between them explicit.

## Verification status

The project contributes no admitted declarations to the accounting, risk,
option-payoff, hedge-floor, or finite-state pricing modules in the public
audit. The exact-rational results are closed under the global context. The
real-valued pricing results inherit Rocq Stdlib's classical real-number and
logic axioms together with functional extensionality.

The exchange matching prototype is intentionally exposed as
`Exchange.Experimental` (and shortened to `Matching` by `All.v`) because it
still contains admitted declarations. Its completed auction and structural
results remain useful, but admitted results must not be treated as certified
until their proof gaps are closed.

The earlier `src/example.v` was a non-buildable duplicate of that prototype.
It is now a compatibility re-export, leaving one maintained source of truth.
