#!/usr/bin/env python3
"""Exact finite stress-scenario checker for the FinShockVerify MVP.

This CLI mirrors the Rocq definitions in theories/Risk/WeightedStress.v using
Python fractions for exact arithmetic. The proof artifact verifies the math;
this script is the first user-facing shape of the tool.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


@dataclass(frozen=True)
class ShockLeg:
    asset: str
    weight: Fraction
    asset_return: Fraction


def parse_fraction(value: str) -> Fraction:
    return Fraction(value.strip())


def load_scenario(path: Path) -> list[ShockLeg]:
    with path.open(newline="") as handle:
        reader = csv.DictReader(handle)
        required = {"asset", "weight", "return"}
        missing = required.difference(reader.fieldnames or [])
        if missing:
            raise ValueError(f"missing CSV columns: {', '.join(sorted(missing))}")

        return [
            ShockLeg(
                asset=row["asset"],
                weight=parse_fraction(row["weight"]),
                asset_return=parse_fraction(row["return"]),
            )
            for row in reader
        ]


def net_weight(scenario: list[ShockLeg]) -> Fraction:
    return sum((leg.weight for leg in scenario), Fraction(0))


def gross_leverage(scenario: list[ShockLeg]) -> Fraction:
    return sum((abs(leg.weight) for leg in scenario), Fraction(0))


def stress_return(scenario: list[ShockLeg]) -> Fraction:
    return sum((leg.weight * leg.asset_return for leg in scenario), Fraction(0))


def format_percent(value: Fraction) -> str:
    return f"{float(value * 100):.4f}% ({value})"


def main() -> int:
    parser = argparse.ArgumentParser(description="Run an exact finite stress check.")
    parser.add_argument("scenario", type=Path, help="CSV with asset,weight,return columns")
    parser.add_argument(
        "--loss-floor",
        type=parse_fraction,
        default=Fraction("-15/100"),
        help="minimum allowed portfolio return, e.g. -15/100",
    )
    args = parser.parse_args()

    scenario = load_scenario(args.scenario)
    ret = stress_return(scenario)
    passes = args.loss_floor <= ret

    print("FinShockVerify stress check")
    print(f"scenario:       {args.scenario}")
    print(f"net weight:     {net_weight(scenario)}")
    print(f"gross leverage: {gross_leverage(scenario)}")
    print(f"stress return:  {format_percent(ret)}")
    print(f"loss floor:     {format_percent(args.loss_floor)}")
    print(f"result:         {'PASS' if passes else 'FAIL'}")

    return 0 if passes else 1


if __name__ == "__main__":
    raise SystemExit(main())
