#!/usr/bin/env python3
"""Exact combinatorial certificate for the spectral Frobenius-kernel resolution.

The script does not prove the module decompositions. It checks all partition,
Gaussian-multinomial, Hilbert-numerator, rank, and Koszul-Betti identities used
in research/notes/SPECTRAL_FROBENIUS_KERNEL_RESOLUTION.md.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import Counter
from functools import lru_cache
from pathlib import Path
from typing import Iterable

Polynomial = list[int]  # coefficient list, low degree first


def trim(poly: Polynomial) -> Polynomial:
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def add(left: Polynomial, right: Polynomial) -> Polynomial:
    size = max(len(left), len(right))
    result = [0] * size
    for index in range(size):
        result[index] = (
            (left[index] if index < len(left) else 0)
            + (right[index] if index < len(right) else 0)
        )
    return trim(result)


def scale(poly: Polynomial, scalar: int) -> Polynomial:
    return trim([scalar * coefficient for coefficient in poly])


def shift(poly: Polynomial, degree: int) -> Polynomial:
    return [0] * degree + poly


def multiply(left: Polynomial, right: Polynomial) -> Polynomial:
    result = [0] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            result[i + j] += x * y
    return trim(result)


@lru_cache(maxsize=None)
def q_binomial(n: int, k: int) -> tuple[int, ...]:
    """Gaussian binomial via the positive recurrence.

    [n choose k]_q = [n-1 choose k]_q
                     + q^(n-k) [n-1 choose k-1]_q.
    """

    if k < 0 or k > n:
        return (0,)
    if k == 0 or k == n:
        return (1,)
    return tuple(
        add(
            list(q_binomial(n - 1, k)),
            shift(list(q_binomial(n - 1, k - 1)), n - k),
        )
    )


def q_multinomial(parts: tuple[int, ...]) -> Polynomial:
    remaining = sum(parts)
    result = [1]
    for part in parts:
        result = multiply(result, list(q_binomial(remaining, part)))
        remaining -= part
    return result


def partitions(total: int, maximum: int | None = None) -> Iterable[tuple[int, ...]]:
    if total == 0:
        yield ()
        return
    if maximum is None or maximum > total:
        maximum = total
    for first in range(maximum, 0, -1):
        for rest in partitions(total - first, min(first, total - first)):
            yield (first,) + rest


def coordinate_orbit_multiplicity(rank: int, partition: tuple[int, ...]) -> int:
    length = len(partition)
    if length > rank:
        return 0
    repeated_part_counts = Counter(partition)
    falling_factorial = math.prod(range(rank - length + 1, rank + 1))
    symmetry_factor = math.prod(
        math.factorial(count) for count in repeated_part_counts.values()
    )
    return falling_factorial // symmetry_factor


def divided_power_numerator(prime: int, rank: int) -> tuple[Polynomial, list[dict]]:
    numerator: Polynomial = [0]
    sectors: list[dict] = []
    for partition in partitions(prime):
        if len(partition) > rank:
            continue
        multiplicity = coordinate_orbit_multiplicity(rank, partition)
        gaussian = q_multinomial(partition)
        numerator = add(numerator, scale(gaussian, multiplicity))
        sectors.append(
            {
                "partition": list(partition),
                "coordinate_orbit_multiplicity": multiplicity,
                "gaussian_multinomial": gaussian,
                "spectral_rank_per_block": sum(gaussian),
            }
        )
    return numerator, sectors


def frobenius_quotient_numerator(prime: int) -> Polynomial:
    result = [1]
    for degree in range(1, prime):
        result = multiply(result, [1] + [0] * (degree - 1) + [-1])
    return result


def subset_degree_polynomial(elements: range, cardinality: int) -> Polynomial:
    result: Polynomial = [0]
    for subset in itertools.combinations(elements, cardinality):
        degree = sum(subset)
        if len(result) <= degree:
            result.extend([0] * (degree + 1 - len(result)))
        result[degree] += 1
    return trim(result)


def resolution(prime: int, rank: int) -> dict:
    divided_numerator, sectors = divided_power_numerator(prime, rank)
    quotient_numerator = frobenius_quotient_numerator(prime)
    kernel_numerator = add(divided_numerator, scale(quotient_numerator, -rank))

    # Remove the r all-same free S summands and then add the generators of
    # I_p=(e_1,...,e_(p-1)) in those same r sectors.
    mixed_free_numerator = divided_numerator.copy()
    mixed_free_numerator[0] -= rank
    mixed_free_numerator = trim(mixed_free_numerator)

    ideal_generator_numerator = scale(
        subset_degree_polynomial(range(1, prime), 1), rank
    )
    free_modules = [add(mixed_free_numerator, ideal_generator_numerator)]

    for homological_degree in range(1, max(1, prime - 1)):
        if homological_degree <= prime - 2:
            free_modules.append(
                scale(
                    subset_degree_polynomial(
                        range(1, prime), homological_degree + 1
                    ),
                    rank,
                )
            )

    alternating_sum: Polynomial = [0]
    for homological_degree, betti_polynomial in enumerate(free_modules):
        alternating_sum = add(
            alternating_sum,
            scale(betti_polynomial, -1 if homological_degree % 2 else 1),
        )

    assert alternating_sum == kernel_numerator
    assert sum(divided_numerator) == rank**prime
    assert math.comb(prime, 1) % prime == 0
    assert all(math.comb(prime, j) % prime == 0 for j in range(1, prime))

    return {
        "prime": prime,
        "rank": rank,
        "spectral_ring_generator_degrees": list(range(1, prime + 1)),
        "coordinate_sectors": sectors,
        "divided_power_hilbert_numerator": divided_numerator,
        "frobenius_quotient_hilbert_numerator": quotient_numerator,
        "kernel_hilbert_numerator": kernel_numerator,
        "minimal_resolution_betti_polynomials": free_modules,
        "alternating_betti_sum": alternating_sum,
        "spectral_rank": sum(divided_numerator),
        "expected_spectral_rank": rank**prime,
        "projective_dimension": max(prime - 2, 0),
        "predicted_depth": prime if prime == 2 else 2,
        "top_syzygy_shift": sum(range(1, prime)),
    }


def parse_cases(raw_cases: list[str]) -> list[tuple[int, int]]:
    cases: list[tuple[int, int]] = []
    for raw in raw_cases:
        try:
            prime_text, rank_text = raw.split(":", maxsplit=1)
            prime = int(prime_text)
            rank = int(rank_text)
        except (ValueError, TypeError) as exc:
            raise argparse.ArgumentTypeError(
                f"invalid case {raw!r}; expected PRIME:RANK"
            ) from exc
        if prime < 2 or rank < 1:
            raise argparse.ArgumentTypeError("prime must be >=2 and rank >=1")
        cases.append((prime, rank))
    return cases


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cases",
        nargs="*",
        default=["2:3", "3:3", "5:5", "7:7"],
        help="prime/rank pairs written PRIME:RANK",
    )
    parser.add_argument(
        "--output",
        default="experiments/spectral_frobenius_resolution_result.json",
    )
    args = parser.parse_args()

    cases = parse_cases(args.cases)
    results = [resolution(prime, rank) for prime, rank in cases]

    ternary = next(item for item in results if item["prime"] == 3 and item["rank"] == 3)
    assert ternary["divided_power_hilbert_numerator"] == [10, 8, 8, 1]
    assert ternary["kernel_hilbert_numerator"] == [7, 11, 11, -2]
    assert ternary["minimal_resolution_betti_polynomials"] == [
        [7, 11, 11, 1],
        [0, 0, 0, 3],
    ]

    binary = next(item for item in results if item["prime"] == 2 and item["rank"] == 3)
    assert binary["divided_power_hilbert_numerator"] == [6, 3]
    assert binary["kernel_hilbert_numerator"] == [3, 6]
    assert binary["projective_dimension"] == 0

    payload = {
        "claim_boundary": (
            "Exact partition and Hilbert-series certificate; this program does "
            "not prove the invariant-module decomposition or minimality of the "
            "mathematical resolution."
        ),
        "formula": {
            "B_p_r": "sum_lambda m(r,lambda) * GaussianMultinomial(p;lambda)",
            "K_p_r": "B_p_r - r * product_{j=1}^{p-1}(1-q^j)",
            "projective_dimension_for_p_ge_3": "p-2",
        },
        "results": results,
    }

    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps(payload, sort_keys=True))


if __name__ == "__main__":
    main()
