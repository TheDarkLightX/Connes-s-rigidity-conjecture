#!/usr/bin/env python3
"""Exact finite-field rank checks for the affine-chart detector theorem.

The source space is the reduced polynomial space of total degree at most d in
r blocks of N variables over F_p.  Chart s fixes block s to (1,0,...,0).
For every subset of charts, the script computes the rank of the joint
restriction map.  A nonzero polynomial can vanish on that subset exactly when
the restriction map has a nontrivial kernel.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import numpy as np


def reduced_monomials(p: int, variables: int, degree: int) -> list[tuple[int, ...]]:
    monomials: list[tuple[int, ...]] = []

    def extend(prefix: tuple[int, ...], remaining_variables: int, remaining_degree: int) -> None:
        if remaining_variables == 0:
            monomials.append(prefix)
            return
        for exponent in range(min(p - 1, remaining_degree) + 1):
            extend(prefix + (exponent,), remaining_variables - 1, remaining_degree - exponent)

    extend((), variables, degree)
    return monomials


def chart_restriction(
    exponent: tuple[int, ...], block_size: int, chart: int
) -> tuple[int, ...] | None:
    start = chart * block_size
    block = exponent[start : start + block_size]
    if any(block[1:]):
        return None
    return exponent[:start] + exponent[start + block_size :]


def rank_mod_p(matrix: np.ndarray, p: int) -> int:
    work = np.asarray(matrix, dtype=np.int64).copy() % p
    rows, columns = work.shape
    pivot_row = 0
    for column in range(columns):
        candidates = np.flatnonzero(work[pivot_row:, column])
        if not len(candidates):
            continue
        selected = pivot_row + int(candidates[0])
        work[[pivot_row, selected]] = work[[selected, pivot_row]]
        inverse = pow(int(work[pivot_row, column]), -1, p)
        work[pivot_row] = (inverse * work[pivot_row]) % p
        for row in range(rows):
            if row == pivot_row or work[row, column] == 0:
                continue
            work[row] = (work[row] - work[row, column] * work[pivot_row]) % p
        pivot_row += 1
        if pivot_row == rows:
            break
    return pivot_row


def restriction_rank(
    p: int,
    rank: int,
    block_size: int,
    monomials: list[tuple[int, ...]],
    charts: tuple[int, ...],
) -> int:
    rows: dict[tuple[int, tuple[int, ...]], int] = {}
    images: list[list[tuple[int, tuple[int, ...]]]] = []
    for exponent in monomials:
        image: list[tuple[int, tuple[int, ...]]] = []
        for chart in charts:
            restricted = chart_restriction(exponent, block_size, chart)
            if restricted is not None:
                key = (chart, restricted)
                rows.setdefault(key, len(rows))
                image.append(key)
        images.append(image)
    matrix = np.zeros((len(rows), len(monomials)), dtype=np.int64)
    for column, image in enumerate(images):
        for key in image:
            matrix[rows[key], column] = 1
    return rank_mod_p(matrix, p)


def analyze_case(p: int, rank: int, block_size: int, degree: int) -> dict[str, object]:
    monomials = reduced_monomials(p, rank * block_size, degree)
    dimension = len(monomials)
    subset_ranks: dict[str, list[int]] = {}
    max_vanishing = 0
    for size in range(rank + 1):
        ranks = []
        for charts in itertools.combinations(range(rank), size):
            chart_rank = restriction_rank(p, rank, block_size, monomials, charts)
            ranks.append(chart_rank)
            if chart_rank < dimension:
                max_vanishing = max(max_vanishing, size)
        subset_ranks[str(size)] = sorted(set(ranks))

    expected_max = min(degree, rank)
    assert max_vanishing == expected_max
    minimum_nonzero_charts = rank - max_vanishing
    assert minimum_nonzero_charts == max(rank - degree, 0)

    return {
        "prime": p,
        "rank": rank,
        "block_size": block_size,
        "degree_bound": degree,
        "source_dimension": dimension,
        "subset_restriction_ranks": subset_ranks,
        "maximum_identically_zero_charts": max_vanishing,
        "minimum_nonzero_charts": minimum_nonzero_charts,
        "expected_minimum_nonzero_charts": max(rank - degree, 0),
        "passed": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).with_name("chart_detector_rank_result.json"),
    )
    args = parser.parse_args()

    cases = [
        (2, 3, 2, 2),
        (2, 4, 2, 2),
        (2, 5, 2, 2),
        (3, 3, 2, 3),
        (3, 4, 2, 3),
        (3, 5, 2, 3),
    ]
    results = [analyze_case(*case) for case in cases]
    payload = {
        "status": "passed",
        "model": "block restriction code for reduced polynomial functions",
        "cases": results,
        "claim_boundary": (
            "Exact finite-field rank evidence for the chart-ideal theorem in the listed cases; "
            "the general statement is proved separately by the monomial block-support argument."
        ),
    }
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, sort_keys=True))


if __name__ == "__main__":
    main()
