#!/usr/bin/env python3
"""Replay stable-range divided-power cyclicity certificates in finite quotients."""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter
from pathlib import Path
from typing import Iterable

Letter = tuple[int, tuple[int, ...]]
Multiset = tuple[Letter, ...]
Vector = dict[Multiset, int]


def monomials(variables: int, degree: int) -> list[tuple[int, ...]]:
    result: list[tuple[int, ...]] = []

    def extend(prefix: tuple[int, ...], left: int, remaining: int) -> None:
        if left == 0:
            result.append(prefix)
            return
        for exponent in range(remaining + 1):
            extend(prefix + (exponent,), left - 1, remaining - exponent)

    extend((), variables, degree)
    return result


def add_exp(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(x + y for x, y in zip(a, b, strict=True))


def unit_exp(variables: int, index: int) -> tuple[int, ...]:
    return tuple(1 if j == index else 0 for j in range(variables))


def normalize(vector: Vector, p: int) -> Vector:
    return {key: value % p for key, value in vector.items() if value % p}


def combine(p: int, *terms: tuple[int, Vector]) -> Vector:
    result: Vector = {}
    for scalar, vector in terms:
        for key, value in vector.items():
            result[key] = (result.get(key, 0) + scalar * value) % p
    return normalize(result, p)


def basis(multiset: Multiset, coefficient: int, p: int) -> Vector:
    coefficient %= p
    return {} if coefficient == 0 else {tuple(sorted(multiset)): coefficient}


def action(
    multiset: Multiset,
    target: int,
    source: int,
    parameter: tuple[int, ...],
    scalar: int,
    p: int,
) -> Vector:
    ordered: dict[tuple[Letter, ...], int] = {}
    for permutation in set(itertools.permutations(multiset)):
        choices: list[list[tuple[Letter, int]]] = []
        for coordinate, exponent in permutation:
            options = [((coordinate, exponent), 1)]
            if coordinate == source:
                options.append(((target, add_exp(exponent, parameter)), scalar % p))
            choices.append(options)
        for selected in itertools.product(*choices):
            output = tuple(item[0] for item in selected)
            coefficient = 1
            for _, weight in selected:
                coefficient = coefficient * weight % p
            ordered[output] = (ordered.get(output, 0) + coefficient) % p

    canonical: Vector = {}
    for output, coefficient in ordered.items():
        sorted_output = tuple(sorted(output))
        canonical_coefficient = ordered.get(sorted_output, 0) % p
        assert coefficient % p == canonical_coefficient
        if canonical_coefficient:
            canonical[sorted_output] = canonical_coefficient
    return canonical


def replace_one(multiset: Multiset, old: Letter, new: Letter) -> Multiset:
    entries = list(multiset)
    entries.remove(old)
    entries.append(new)
    return tuple(sorted(entries))


def total_degree(multiset: Multiset) -> int:
    return sum(sum(exponent) for _, exponent in multiset)


def all_multisets(p: int, rank: int, variables: int, degree: int) -> list[Multiset]:
    letters = [(coordinate, exponent) for coordinate in range(rank)
               for exponent in monomials(variables, degree)]
    return [
        tuple(candidate)
        for candidate in itertools.combinations_with_replacement(letters, p)
        if total_degree(candidate) <= degree
    ]


def verify_case(p: int, rank: int, variables: int, degree: int) -> dict[str, object]:
    assert p >= 2
    assert rank >= p
    assert rank > p or p % 2 == 1
    zero = (0,) * variables
    inverse_two = pow(2, -1, p) if p % 2 == 1 else None
    divided_power_basis = all_multisets(p, rank, variables, degree)
    kernel_basis = [candidate for candidate in divided_power_basis
                    if len(set(candidate)) != 1]

    ledger = Counter()
    for target_multiset in sorted(
        kernel_basis,
        key=lambda item: (total_degree(item), -len({coordinate for coordinate, _ in item}), item),
    ):
        degree_now = total_degree(target_multiset)
        labels = [coordinate for coordinate, _ in target_multiset]
        distinct_labels = set(labels)

        if degree_now == 0:
            if len(distinct_labels) == p:
                # Every constant p-frame is in the SL_rank(F_p)-orbit span of
                # the standard frame.  At rank p this is the unique frame.
                ledger["constant_frame_orbit"] += 1
                continue

            counts = Counter(target_multiset)
            repeated_letter = next(letter for letter, count in counts.items() if count >= 2)
            target_coordinate, _ = repeated_letter
            fresh_coordinate = next(coordinate for coordinate in range(rank)
                                    if coordinate not in distinct_labels)
            source_multiset = replace_one(
                target_multiset, repeated_letter, (fresh_coordinate, zero)
            )
            difference = combine(
                p,
                (1, action(source_multiset, target_coordinate, fresh_coordinate, zero, 1, p)),
                (-1, basis(source_multiset, 1, p)),
            )
            coefficient = counts[repeated_letter] % p
            assert difference == basis(target_multiset, coefficient, p)
            assert coefficient != 0
            assert len({coordinate for coordinate, _ in source_multiset}) == len(distinct_labels) + 1
            ledger["constant_collision"] += 1
            continue

        positive_entries = [letter for letter in target_multiset if sum(letter[1]) > 0]
        selected: Letter | None = None
        fresh_coordinate: int | None = None
        for letter in positive_entries:
            other_entries = list(target_multiset)
            other_entries.remove(letter)
            other_labels = {coordinate for coordinate, _ in other_entries}
            candidates = [coordinate for coordinate in range(rank)
                          if coordinate != letter[0] and coordinate not in other_labels]
            if candidates:
                selected = letter
                fresh_coordinate = candidates[0]
                break

        if selected is not None and fresh_coordinate is not None:
            coordinate, exponent = selected
            variable = next(index for index, value in enumerate(exponent) if value > 0)
            lowered = list(exponent)
            lowered[variable] -= 1
            source_letter = (fresh_coordinate, tuple(lowered))
            source_multiset = replace_one(target_multiset, selected, source_letter)
            difference = combine(
                p,
                (1, action(source_multiset, coordinate, fresh_coordinate,
                           unit_exp(variables, variable), 1, p)),
                (-1, basis(source_multiset, 1, p)),
            )
            coefficient = Counter(target_multiset)[selected] % p
            assert difference == basis(target_multiset, coefficient, p)
            assert coefficient != 0
            assert total_degree(source_multiset) == degree_now - 1
            ledger["repeated_label_induction"] += 1
            continue

        # The only no-fresh-coordinate case in the supported range is the
        # critical odd-prime diagonal rank=p with all coordinate labels used.
        assert rank == p and p % 2 == 1 and len(distinct_labels) == p
        assert inverse_two is not None
        by_coordinate = {coordinate: exponent for coordinate, exponent in target_multiset}
        target_coordinate = next(
            coordinate for coordinate, exponent in by_coordinate.items() if sum(exponent) > 0
        )
        source_coordinate = next(coordinate for coordinate in range(rank)
                                 if coordinate != target_coordinate)
        x = by_coordinate[target_coordinate]
        y = by_coordinate[source_coordinate]
        other_letters = tuple(
            (coordinate, by_coordinate[coordinate])
            for coordinate in range(rank)
            if coordinate not in {target_coordinate, source_coordinate}
        )
        source_multiset = tuple(sorted(
            ((source_coordinate, zero), (source_coordinate, y)) + other_letters
        ))
        positive_action = action(
            source_multiset, target_coordinate, source_coordinate, x, 1, p
        )
        negative_action = action(
            source_multiset, target_coordinate, source_coordinate, x, -1, p
        )
        linear_part = combine(p, (inverse_two, combine(p, (1, positive_action), (-1, negative_action))))
        if y == zero:
            assert linear_part == basis(target_multiset, 1, p)
            ledger["equal_source"] += 1
        else:
            auxiliary = tuple(sorted(
                ((target_coordinate, add_exp(x, y)), (source_coordinate, zero))
                + other_letters
            ))
            expected = combine(
                p,
                (1, basis(target_multiset, 1, p)),
                (1, basis(auxiliary, 1, p)),
            )
            assert linear_part == expected

            equal_source_multiset = tuple(sorted(
                ((source_coordinate, zero), (source_coordinate, zero)) + other_letters
            ))
            equal_positive = action(
                equal_source_multiset, target_coordinate, source_coordinate,
                add_exp(x, y), 1, p
            )
            equal_negative = action(
                equal_source_multiset, target_coordinate, source_coordinate,
                add_exp(x, y), -1, p
            )
            auxiliary_linear = combine(
                p,
                (inverse_two, combine(p, (1, equal_positive), (-1, equal_negative))),
            )
            assert auxiliary_linear == basis(auxiliary, 1, p)
            ledger["distinct_source_two_step"] += 1

    assert sum(ledger.values()) == len(kernel_basis)
    return {
        "prime": p,
        "rank": rank,
        "polynomial_variables": variables,
        "max_total_degree": degree,
        "divided_power_dimension": len(divided_power_basis),
        "frobenius_kernel_dimension": len(kernel_basis),
        "certificate_ledger": dict(sorted(ledger.items())),
        "certificate_total": sum(ledger.values()),
        "all_kernel_basis_vectors_certified": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, default=5)
    parser.add_argument("--rank", type=int)
    parser.add_argument("--variables", type=int, default=1)
    parser.add_argument("--degree", type=int, default=2)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).with_name("odd_prime_divided_power_result.json"),
    )
    args = parser.parse_args()
    rank = args.prime if args.rank is None else args.rank
    result = verify_case(args.prime, rank, args.variables, args.degree)
    payload = {
        "status": "passed",
        "model": "finite total-degree quotient of the divided p-th power multiset basis",
        "result": result,
        "claim_boundary": (
            "Every basis vector in the declared finite quotient has a replayed local certificate; "
            "the untruncated stable/critical-range cyclicity theorem remains a paper proof candidate."
        ),
    }
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, sort_keys=True))


if __name__ == "__main__":
    main()
