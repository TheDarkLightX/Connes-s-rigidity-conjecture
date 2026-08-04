#!/usr/bin/env python3
"""Multivariate F_3 divided-cube orbit and proof-certificate oracle.

The default model is R = F_3[t_1,t_2] through total degree three.  Besides
closing the constant all-distinct tensor under elementary monomial
transvections, it replays the simultaneous-induction identities used by the
multivariate cyclicity proof candidate.
"""

from __future__ import annotations

import argparse
import json
from itertools import permutations
from pathlib import Path

import numpy as np

from divided_cube_graded_orbit import RowBasis, apply_sparse_columns


P = 3


def exponent_vectors(variables: int, max_degree: int):
    def fixed_sum(slots: int, total: int):
        if slots == 1:
            yield (total,)
            return
        for first in range(total + 1):
            for tail in fixed_sum(slots - 1, total - first):
                yield (first,) + tail

    return [
        exponent
        for degree in range(max_degree + 1)
        for exponent in fixed_sum(variables, degree)
    ]


def exponent_add(left, right):
    return tuple(a + b for a, b in zip(left, right, strict=True))


def total_degree(multiset):
    return sum(sum(exponent) for _, exponent in multiset)


def canonical(letters):
    return tuple(sorted(letters, key=lambda x: (sum(x[1]), x[1], x[0])))


def distinct_permutations(xs):
    return sorted(set(permutations(xs)))


def build_basis(variables: int, max_degree: int):
    monomials = exponent_vectors(variables, max_degree)
    letters = [(coordinate, exponent) for exponent in monomials for coordinate in range(3)]
    basis = []
    for a_index, a in enumerate(letters):
        for b_index in range(a_index, len(letters)):
            b = letters[b_index]
            for c_index in range(b_index, len(letters)):
                c = letters[c_index]
                multiset = (a, b, c)
                if total_degree(multiset) <= max_degree:
                    basis.append(multiset)
    index = {multiset: j for j, multiset in enumerate(basis)}
    kernel = [
        j for j, multiset in enumerate(basis)
        if not (multiset[0] == multiset[1] == multiset[2])
    ]
    return monomials, basis, index, kernel


def action_column(multiset, target, source, shift, index, amplitude=1):
    ordered_coefficients = {}
    for ordered in distinct_permutations(multiset):
        terms = [((), 1)]
        for coordinate, exponent in ordered:
            choices = [((coordinate, exponent), 1)]
            if coordinate == source:
                choices.append(
                    ((target, exponent_add(exponent, shift)), amplitude % P)
                )
            terms = [
                (prefix + (letter,), coefficient * scalar)
                for prefix, coefficient in terms
                for letter, scalar in choices
            ]
        for ordered_output, coefficient in terms:
            ordered_coefficients[ordered_output] = (
                ordered_coefficients.get(ordered_output, 0) + coefficient
            ) % P

    output = {}
    for output_multiset in {canonical(x) for x in ordered_coefficients}:
        coefficient = ordered_coefficients.get(output_multiset, 0) % P
        if coefficient and output_multiset in index:
            output[index[output_multiset]] = coefficient
    return output


def sparse_subtract(left, right):
    output = {}
    for coordinate in set(left) | set(right):
        coefficient = (left.get(coordinate, 0) - right.get(coordinate, 0)) % P
        if coefficient:
            output[coordinate] = coefficient
    return output


def finite_difference(multiset, target, source, shift, index):
    return sparse_subtract(
        action_column(multiset, target, source, shift, index, amplitude=2),
        action_column(multiset, target, source, shift, index, amplitude=1),
    )


def verify_proof_certificates(variables, basis, index, kernel):
    zero = (0,) * variables
    w = canonical(((0, zero), (1, zero), (2, zero)))
    constant_checks = 0
    repeated_checks = 0
    equal_source_checks = 0
    two_step_checks = 0

    for target in range(3):
        for source in range(3):
            if target == source:
                continue
            remaining = ({0, 1, 2} - {target, source}).pop()
            observed = sparse_subtract(
                action_column(w, target, source, zero, index),
                {index[w]: 1},
            )
            expected = canonical(
                ((target, zero), (target, zero), (remaining, zero))
            )
            assert observed == {index[expected]: 2}
            constant_checks += 1

    for basis_index in kernel:
        multiset = basis[basis_index]
        labels = [letter[0] for letter in multiset]
        if len(set(labels)) == 3 or total_degree(multiset) == 0:
            continue
        found = False
        for position, (target, exponent) in enumerate(multiset):
            for variable, power in enumerate(exponent):
                if power == 0:
                    continue
                other_labels = {
                    letter[0] for j, letter in enumerate(multiset) if j != position
                }
                for fresh in range(3):
                    if fresh == target or fresh in other_labels:
                        continue
                    lower = list(exponent)
                    lower[variable] -= 1
                    shift = tuple(int(j == variable) for j in range(variables))
                    source_letters = list(multiset)
                    source_letters[position] = (fresh, tuple(lower))
                    source_multiset = canonical(source_letters)
                    observed = sparse_subtract(
                        action_column(source_multiset, target, fresh, shift, index),
                        {index[source_multiset]: 1},
                    )
                    if observed in ({basis_index: 1}, {basis_index: 2}):
                        found = True
                        break
                if found:
                    break
            if found:
                break
        assert found, multiset
        repeated_checks += 1

    for basis_index, multiset in enumerate(basis):
        by_coordinate = {coordinate: exponent for coordinate, exponent in multiset}
        if len(by_coordinate) != 3 or multiset == w:
            continue
        x, y, z = (by_coordinate[j] for j in range(3))
        if y == zero:
            source_multiset = canonical(((1, zero), (1, zero), (2, z)))
            assert finite_difference(
                source_multiset, 0, 1, x, index
            ) == {basis_index: 1}
            equal_source_checks += 1
            continue

        source_multiset = canonical(((1, zero), (1, y), (2, z)))
        product = exponent_add(x, y)
        auxiliary = canonical(((0, product), (1, zero), (2, z)))
        assert finite_difference(source_multiset, 0, 1, x, index) == {
            basis_index: 1,
            index[auxiliary]: 1,
        }
        equal_source = canonical(((1, zero), (1, zero), (2, z)))
        assert finite_difference(equal_source, 0, 1, product, index) == {
            index[auxiliary]: 1
        }
        assert total_degree(source_multiset) <= total_degree(multiset)
        assert total_degree(equal_source) <= total_degree(multiset)
        two_step_checks += 1

    return {
        "generator_seed_checks": 1,
        "constant_collision_coefficient_checks": constant_checks,
        "repeated_label_induction_checks": repeated_checks,
        "equal_source_direct_checks": equal_source_checks,
        "distinct_source_two_step_checks": two_step_checks,
        "simultaneous_induction_certificate": True,
    }


def analyze(variables: int, max_degree: int):
    monomials, basis, index, kernel = build_basis(variables, max_degree)
    certificates = verify_proof_certificates(
        variables, basis, index, kernel
    )
    generators = [
        (target, source, shift)
        for target in range(3)
        for source in range(3)
        if target != source
        for shift in monomials
    ]
    actions = [
        [action_column(multiset, *generator, index) for multiset in basis]
        for generator in generators
    ]

    zero = (0,) * variables
    w = canonical(((0, zero), (1, zero), (2, zero)))
    seed = np.zeros(len(basis), dtype=np.int8)
    seed[index[w]] = 1
    span = RowBasis(len(basis))
    queue = [span.add(seed)]
    position = 0
    while position < len(queue):
        vector = queue[position]
        position += 1
        for columns in actions:
            new = span.add(apply_sparse_columns(vector, columns))
            if new is not None:
                queue.append(new)

    return {
        "field": "F_3",
        "ring": f"F_3[t_1,...,t_{variables}]",
        "variables": variables,
        "max_total_degree": max_degree,
        "generator_count": len(generators),
        "divided_cube_dimension": len(basis),
        "frobenius_kernel_dimension": len(kernel),
        "orbit_span_dimension": len(span.rows),
        "orbit_span_equals_kernel": len(span.rows) == len(kernel),
        "proof_certificate_checks": certificates,
        "claim_boundary": (
            "Exact finite quotient evidence; the untruncated multivariate "
            "statement remains a paper proof candidate."
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--variables", type=int, default=2)
    parser.add_argument("--degree", type=int, default=3)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("experiments/divided_cube_multivariate_orbit_result.json"),
    )
    args = parser.parse_args()
    result = analyze(args.variables, args.degree)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result))
    assert result["orbit_span_equals_kernel"]


if __name__ == "__main__":
    main()
