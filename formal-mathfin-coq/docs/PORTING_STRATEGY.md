# Porting strategy

## Why this is not a source-to-source translation

Lean's Mathlib and Rocq's ecosystem expose different definitions and theorem
interfaces for finite sums, real analysis, measure theory, probability, and
topology. A syntactically translated proof can therefore compile while proving
a subtly different statement—or fail even when the mathematics is already
available under a different abstraction.

The unit of migration is a declaration together with:

1. its source commit and Lean name;
2. its Rocq name and statement;
3. the representation changes made during the port;
4. its faithfulness status;
5. the assumptions reported by Rocq.

## Faithfulness statuses

The ledger follows the upstream library's terminology:

- `full`: the Rocq statement is the same mathematical claim, allowing an
  explicitly documented equivalent representation;
- `library_wrapper`: a thin exported name for a theorem supplied upstream;
- `reduced_core`: the Rocq theorem requires an added hypothesis or proves only
  a restricted form;
- `placeholder`: no proof has been completed.

Only `full` and `library_wrapper` declarations count as completed ports.

## Dependency stages

### Stage 1: finite algebraic finance

Use only Rocq's standard library:

- finite-state pricing;
- payoff identities and static no-arbitrage;
- finite binomial models;
- elementary portfolio and risk identities;
- fixed-income cash-flow algebra.

This stage gives fast kernel-checked progress without committing the analytic
layers to an unsuitable representation.

### Stage 2: real analysis and closed forms

Run a focused compatibility spike comparing:

- Rocq standard `Reals`;
- Coquelicot;
- MathComp-Analysis.

The decision must cover exponential/logarithm identities, derivatives,
integrals, Gaussian density/CDF definitions, and finite-dimensional linear
algebra. Black-Scholes closed forms should not be ported before this decision.

### Stage 3: probability and measure changes

Choose one measure/probability foundation and port:

- expectations and conditional expectations;
- martingales and filtrations;
- Radon-Nikodym/change of measure;
- finite and one-period FTAP results.

### Stage 4: stochastic calculus

Build or reuse the infrastructure needed for:

- Brownian motion;
- adapted simple processes;
- the L2 Ito isometry and completion;
- quadratic variation and Ito's formula;
- Girsanov and continuous-time pricing.

This is the largest research stage and should be treated as a separate
verified library program, not estimated as routine translation work.

## Initial representation decision

The Lean source uses `Finset ι`. The first Rocq slice uses `list I` and a
recursive finite sum. This is conservative:

- with `NoDup states`, it is the direct finite-set interpretation;
- without `NoDup`, the theorems remain valid for a finite multiset of states.

No theorem relies on duplicate states, and the representation change is
recorded in the ledger.

## Suggested next slice

Port `Foundations/TriangleArbitrage.lean` and the finite-state portion of
`Foundations/PricingKernel.lean`, then introduce a small generic linear-pricing
record. That tests whether subsequent option theorems can reuse one structural
pricing interface rather than accumulating ad-hoc finite sums.
