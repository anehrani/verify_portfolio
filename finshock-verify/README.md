# FinShockVerify

FinShockVerify is a Rocq/Coq-style verification MVP for portfolio changes under
price jumps. It proves small but commercially relevant facts about portfolio
accounting, finite stress scenarios, and loss floors.

The MVP uses exact rational arithmetic and finite scenarios first. That keeps
the proof surface practical and avoids pretending that a theorem prover can
predict markets.

## What Is Included

- `theories/Core/SingleAsset.v`
  - cash, shares, price, portfolio value
  - price-jump transition
  - trade transition with explicit fee
  - proofs of self-financing accounting and price-jump PnL

- `theories/Risk/WeightedStress.v`
  - finite weighted stress scenarios
  - net weight, gross leverage, stress return
  - boolean loss-floor checker
  - proof that the checker is sound
  - proof of a long-only fully invested loss-floor theorem

- `theories/Options/CryptoProtectivePut.v`
  - crypto spot plus long-put payoff model
  - proof that a matching protective put gives a terminal value floor at strike
  - proof that protected terminal wealth is bounded below by cash minus premium
    plus units times strike

- `theories/Options/Vanilla.v`
  - reusable vanilla call/put payoff definitions
  - option leg and option book aggregation
  - nonnegativity theorems for long option payoffs

- `theories/Options/PortfolioValidation.v`
  - hedge coverage predicates
  - covered protective-put terminal wealth floor theorem
  - generic validation foundation for option hedged portfolios

- `theories/Examples/LongOnlyETF.v`
  - checked 70/30 equity-bond scenario

- `tools/stress_check.py`
  - exact-arithmetic CLI that mirrors the finite stress definitions

- `tools/protective_put_check.py`
  - exact-arithmetic CLI for covered protective-put validation

## Build The Proofs

```sh
make build
```

## Run The Example CLI

```sh
python3 tools/stress_check.py examples/long_only_stress.csv --loss-floor=-15/100
```

Expected result:

```text
FinShockVerify stress check
net weight:     1
gross leverage: 1
stress return:  -13.1000% (-131/1000)
loss floor:     -15.0000% (-3/20)
result:         PASS
```

## Run The Protective Put Validator

```sh
python3 tools/protective_put_check.py \
  --cash 0 \
  --premium 5000 \
  --spot-units 1 \
  --put-units 1 \
  --final-spot 30000 \
  --strike 80000
```

Expected result:

```text
covered hedge:  YES
wealth floor:   75,000.00 (75000)
terminal wealth: 75,000.00 (75000)
result:         PASS
```

## MVP Thesis

The first product should verify this claim:

> Given portfolio weights, finite price-jump scenarios, and rebalancing/risk
> rules, FinShockVerify proves that the executable checks preserve the intended
> accounting and risk invariants.

For crypto option hedged portfolios, the first specialized claim is:

> Given a valid and enforceable long put option that settles according to its
> payoff definition, FinShockVerify proves that a matching long-crypto
> protective-put portfolio has a terminal downside floor at the option strike,
> net of explicitly modeled premium and cash.

That is useful for model validation, risk governance, DeFi protocols, and
portfolio-management infrastructure.

## Research Path

See `docs/PAPER_SKETCH.md` for a paper outline and `docs/MVP_ROADMAP.md` for
the next implementation milestones. See
`docs/OPTION_PORTFOLIO_VALIDATION_FOUNDATION.md` for the option-validation
architecture.
