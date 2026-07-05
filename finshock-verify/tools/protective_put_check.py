#!/usr/bin/env python3
"""Exact protective-put validation check.

This CLI mirrors the covered protective-put definitions in
theories/Options/PortfolioValidation.v. It is an operational adapter, not a
replacement for the Rocq proofs.
"""

from __future__ import annotations

import argparse
from fractions import Fraction


def parse_fraction(value: str) -> Fraction:
    return Fraction(value.strip())


def put_payoff(final_spot: Fraction, strike: Fraction) -> Fraction:
    return max(strike - final_spot, Fraction(0))


def protected_value(
    spot_units: Fraction,
    put_units: Fraction,
    final_spot: Fraction,
    strike: Fraction,
) -> Fraction:
    return spot_units * final_spot + put_units * put_payoff(final_spot, strike)


def protected_wealth(
    cash: Fraction,
    premium: Fraction,
    spot_units: Fraction,
    put_units: Fraction,
    final_spot: Fraction,
    strike: Fraction,
) -> Fraction:
    return cash - premium + protected_value(spot_units, put_units, final_spot, strike)


def format_money(value: Fraction) -> str:
    return f"{float(value):,.2f} ({value})"


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate an exact protective-put terminal wealth floor."
    )
    parser.add_argument("--cash", type=parse_fraction, default=Fraction(0))
    parser.add_argument("--premium", type=parse_fraction, required=True)
    parser.add_argument("--spot-units", type=parse_fraction, required=True)
    parser.add_argument("--put-units", type=parse_fraction, required=True)
    parser.add_argument("--final-spot", type=parse_fraction, required=True)
    parser.add_argument("--strike", type=parse_fraction, required=True)
    args = parser.parse_args()

    floor = args.cash - args.premium + args.spot_units * args.strike
    wealth = protected_wealth(
        args.cash,
        args.premium,
        args.spot_units,
        args.put_units,
        args.final_spot,
        args.strike,
    )
    covers = Fraction(0) <= args.spot_units <= args.put_units
    passes = covers and floor <= wealth

    print("FinShockVerify protective put check")
    print(f"cash:           {format_money(args.cash)}")
    print(f"premium:        {format_money(args.premium)}")
    print(f"spot units:     {args.spot_units}")
    print(f"put units:      {args.put_units}")
    print(f"final spot:     {format_money(args.final_spot)}")
    print(f"strike:         {format_money(args.strike)}")
    print(f"covered hedge:  {'YES' if covers else 'NO'}")
    print(f"wealth floor:   {format_money(floor)}")
    print(f"terminal wealth: {format_money(wealth)}")
    print(f"result:         {'PASS' if passes else 'FAIL'}")

    return 0 if passes else 1


if __name__ == "__main__":
    raise SystemExit(main())
