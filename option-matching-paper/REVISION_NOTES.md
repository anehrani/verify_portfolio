# Revision notes

## Central editorial change

The original manuscript described a fully verified matching and clearing
system while Section 12 and the Coq source showed that most headline results
were still theorem targets. The revision changes the title and contribution
claim to a verification blueprint with an audited prototype.

## How the Lean reference paper was used

The revision adopts the reference paper's strongest methodological idea:

- every declaration is classified as `full`, `library_wrapper`,
  `reduced_core`, or `placeholder`;
- paper-facing claims are separated from simplified algebraic cores;
- completed headline results are checked with `Print Assumptions`;
- `rocq check` exposes admitted declarations in the module context;
- only `full` and `library_wrapper` results count as completed.

The reference paper is now discussed as complementary work: it verifies
mathematical-finance and pricing foundations, while this paper targets
option-market microstructure.

## Claim corrections

- Replaced "verified theorem" language with "proof obligation" for
  unmechanized end-to-end results.
- Distinguished candidate-price maximality from a verified opening-auction
  allocation mechanism.
- Classified `no_broken_strategy` as a reduced core because fills are defined
  directly from one common scale rather than produced by an executable complex
  matcher.
- Reported six admitted declarations explicitly.
- Rewrote the abstract, contributions, scope, evaluation, limitations, and
  conclusion around the evidence the artifact currently supplies.
- Replaced normalized-fill division in the no-broken-strategy statement with a
  cross-multiplication formulation.

## Artifact corrections

- Updated imports for Rocq 9.1.
- Made the copied prototype compile.
- Added a reproducible build and kernel audit.
- Added `verification_ledger.csv`.

## Highest-priority proof work

1. Prove the recursive residual-quantity invariant.
2. Prove sorting/filter permutation lemmas.
3. Complete end-to-end contract consistency and no overfill.
4. Implement and verify limit respect, expiry validity, tick validity, and
   price-time fairness.
5. Construct an actual uniform opening allocation, not only an optimal price.
6. Connect the shared package-scale core to an executable complex-order
   matcher and prove its liquidity bound.
