# Formal MathFin for Rocq/Coq

This directory is a staged Rocq/Coq port of Raphael Coelho's
[`formal-mathfin`](https://github.com/raphaelrrcoelho/formal-mathfin) Lean 4
library.

The port is intentionally theorem-by-theorem. Lean and Rocq have different
mathematical libraries, so translating syntax without recording changes in
definitions, hypotheses, or proof dependencies would give a misleading result.
Every ported declaration therefore has an entry in
[`porting_ledger.csv`](porting_ledger.csv).

## Pinned upstream

The initial port targets:

- repository: `https://github.com/raphaelrrcoelho/formal-mathfin`
- commit: `d7766e48e2f4761df26e0885bfeea14571d973c6`
- Lean source files: 227
- Rocq version used here: 9.1.1

See [`UPSTREAM.lock`](UPSTREAM.lock) and
[`docs/PORTING_STRATEGY.md`](docs/PORTING_STRATEGY.md).

## Implemented first slice

The initial vertical slice ports the finite-state, no-arbitrage foundation:

- `Foundations/StatePrices.v`
  - Arrow-Debreu state-price valuation
  - zero, unit, constant, additive, and homogeneous payoff laws
  - risk-neutral consistency
  - non-negativity of prices
- `Foundations/NoArbitrageDerivations.v`
  - positive-part payoff identity
  - put-call parity from state-price valuation
  - fair-forward characterization and uniqueness
- `AxiomAudit.v`
  - explicit `Print Assumptions` checks for the load-bearing theorems

The finite Lean `Finset` is represented by a Rocq `list`. The resulting
theorems are valid even if the list contains duplicates; restricting to
duplicate-free lists recovers the exact finite-set interpretation.

## Build and verify

```sh
make build
make audit
```

`make build` compiles every listed source file. `make audit` asks Rocq's kernel
checker to re-check the compiled audit module and print its assumption
context. The current result and the distinction between theorem-level and
transitive module assumptions are recorded in
[`docs/AXIOM_AUDIT.md`](docs/AXIOM_AUDIT.md).

## Scope

This is the beginning of a port, not a claim that the full Lean library has
already been reproduced. In particular, stochastic integration, measure
changes, Brownian motion, and continuous-time asset pricing require an
explicit Rocq analysis/probability dependency decision before they can be
ported faithfully.
