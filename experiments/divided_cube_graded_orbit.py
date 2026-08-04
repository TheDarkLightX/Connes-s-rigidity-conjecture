#!/usr/bin/env python3
"""Total-degree orbit oracle for the ternary divided-cube kernel.

For a cutoff D, this computes over F_3 in the quotient spanned by multiset
tensors of total polynomial degree at most D.  It closes the all-distinct
constant tensor under every elementary monomial transvection

    I + t^r E_ij,  i != j,  0 <= r <= D,

and compares the resulting span with the full non-diagonal Frobenius kernel.
The calculation is finite evidence for cyclicity, not a proof at D = infinity.
"""

from __future__ import annotations

import argparse
import json
from itertools import permutations
from pathlib import Path

import numpy as np


P = 3


def canonical(letters):
    return tuple(sorted(letters, key=lambda x: (x[1], x[0])))


def distinct_permutations(xs):
    return sorted(set(permutations(xs)))


def build_basis(max_degree: int):
    letters = [(coordinate, degree)
               for degree in range(max_degree + 1)
               for coordinate in range(3)]
    basis = []
    for a_index, a in enumerate(letters):
        for b_index in range(a_index, len(letters)):
            b = letters[b_index]
            for c_index in range(b_index, len(letters)):
                c = letters[c_index]
                if a[1] + b[1] + c[1] <= max_degree:
                    basis.append((a, b, c))
    index = {multiset: j for j, multiset in enumerate(basis)}
    kernel = [
        j for j, multiset in enumerate(basis)
        if not (multiset[0] == multiset[1] == multiset[2])
    ]
    return basis, index, kernel


def action_column(
    multiset, target: int, source: int, shift: int, index, amplitude: int = 1
):
    """Sparse action column for I + amplitude*t^shift E_target,source."""
    ordered_coefficients = {}
    for ordered in distinct_permutations(multiset):
        terms = [((), 1)]
        for coordinate, degree in ordered:
            choices = [((coordinate, degree), 1)]
            if coordinate == source:
                choices.append(((target, degree + shift), amplitude % P))
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
        # Equivariance makes the coefficient equal on every ordering, so one
        # canonical representative is the orbit-sum coefficient.
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


def verify_proof_certificates(max_degree, basis, index, kernel):
    """Replay the local identities in the simultaneous cyclicity induction."""
    constant_checks = 0
    repeated_induction_checks = 0
    finite_difference_checks = 0

    w = canonical(((0, 0), (1, 0), (2, 0)))
    generator_seed_checks = int(w in index)
    assert generator_seed_checks == 1
    for target in range(3):
        for source in range(3):
            if target == source:
                continue
            remaining = ({0, 1, 2} - {target, source}).pop()
            observed = sparse_subtract(
                action_column(w, target, source, 0, index),
                {index[w]: 1},
            )
            expected_multiset = canonical(
                ((target, 0), (target, 0), (remaining, 0))
            )
            assert observed == {index[expected_multiset]: 2}
            constant_checks += 1

    for basis_index in kernel:
        multiset = basis[basis_index]
        labels = [letter[0] for letter in multiset]
        total_degree = sum(letter[1] for letter in multiset)
        if len(set(labels)) == 3 or total_degree == 0:
            continue
        found_certificate = False
        for position, (target, degree) in enumerate(multiset):
            if degree == 0:
                continue
            other_labels = {
                letter[0] for j, letter in enumerate(multiset) if j != position
            }
            for fresh_label in range(3):
                if fresh_label == target or fresh_label in other_labels:
                    continue
                source_letters = list(multiset)
                source_letters[position] = (fresh_label, degree - 1)
                source_multiset = canonical(source_letters)
                observed = sparse_subtract(
                    action_column(source_multiset, target, fresh_label, 1, index),
                    {index[source_multiset]: 1},
                )
                if observed in (
                    {basis_index: 1},
                    {basis_index: 2},
                ):
                    found_certificate = True
                    break
            if found_certificate:
                break
        assert found_certificate, multiset
        repeated_induction_checks += 1

    for basis_index, multiset in enumerate(basis):
        if multiset == w:
            continue
        by_coordinate = {coordinate: degree for coordinate, degree in multiset}
        if len(by_coordinate) != 3:
            continue
        a, b, c = (by_coordinate[j] for j in range(3))
        if a >= b:
            target, source, x_degree, shift = 0, 1, b, a - b
        else:
            target, source, x_degree, shift = 1, 0, a, b - a
        remaining = ({0, 1, 2} - {target, source}).pop()
        source_multiset = canonical(
            ((source, x_degree), (source, x_degree), (remaining, c))
        )
        observed = sparse_subtract(
            action_column(
                source_multiset, target, source, shift, index, amplitude=2
            ),
            action_column(
                source_multiset, target, source, shift, index, amplitude=1
            ),
        )
        assert observed == {basis_index: 1}, (multiset, observed)
        assert sum(letter[1] for letter in source_multiset) <= sum(
            letter[1] for letter in multiset
        )
        finite_difference_checks += 1

    return {
        "generator_seed_checks": generator_seed_checks,
        "constant_collision_coefficient_checks": constant_checks,
        "repeated_label_induction_checks": repeated_induction_checks,
        "equal_source_finite_difference_checks": finite_difference_checks,
        "simultaneous_induction_certificate": True,
    }


class RowBasis:
    """Incremental row echelon basis over F_3."""

    def __init__(self, dimension: int):
        self.dimension = dimension
        self.rows = {}

    def reduce(self, vector):
        vector = vector.copy() % P
        while True:
            nonzero = np.flatnonzero(vector)
            if len(nonzero) == 0:
                return vector
            pivot = int(nonzero[0])
            row = self.rows.get(pivot)
            if row is None:
                return vector
            vector = (vector - vector[pivot] * row) % P

    def add(self, vector):
        vector = self.reduce(vector)
        nonzero = np.flatnonzero(vector)
        if len(nonzero) == 0:
            return None
        pivot = int(nonzero[0])
        vector = (vector * (1 if vector[pivot] == 1 else 2)) % P
        self.rows[pivot] = vector
        return vector


def apply_sparse_columns(vector, columns):
    output = np.zeros_like(vector)
    for column in np.flatnonzero(vector):
        scalar = int(vector[column])
        for row, coefficient in columns[int(column)].items():
            output[row] = (output[row] + scalar * coefficient) % P
    return output


def analyze(max_degree: int):
    basis, index, kernel = build_basis(max_degree)
    proof_certificates = verify_proof_certificates(
        max_degree, basis, index, kernel
    )
    dimension = len(basis)
    generators = [
        (target, source, shift)
        for target in range(3)
        for source in range(3)
        if target != source
        for shift in range(max_degree + 1)
    ]
    actions = [
        [action_column(multiset, *generator, index) for multiset in basis]
        for generator in generators
    ]

    all_distinct = canonical(((0, 0), (1, 0), (2, 0)))
    seed = np.zeros(dimension, dtype=np.int8)
    seed[index[all_distinct]] = 1
    span = RowBasis(dimension)
    queue = [span.add(seed)]
    position = 0
    while position < len(queue):
        vector = queue[position]
        position += 1
        for columns in actions:
            new = span.add(apply_sparse_columns(vector, columns))
            if new is not None:
                queue.append(new)

    degree_table = []
    for degree in range(max_degree + 1):
        divided_dimension = sum(
            sum(letter[1] for letter in multiset) == degree
            for multiset in basis
        )
        kernel_dimension = sum(
            sum(letter[1] for letter in basis[j]) == degree
            for j in kernel
        )
        degree_table.append({
            "total_degree": degree,
            "divided_cube_dimension": divided_dimension,
            "frobenius_kernel_dimension": kernel_dimension,
        })

    return {
        "field": "F_3",
        "model": "total-degree quotient of the multiset basis of Gamma^3(F_3[t]^3)",
        "max_total_degree": max_degree,
        "generator_count": len(generators),
        "divided_cube_dimension": dimension,
        "frobenius_kernel_dimension": len(kernel),
        "all_distinct_orbit_span_dimension": len(span.rows),
        "all_distinct_generates_projected_kernel": len(span.rows) == len(kernel),
        "proof_certificate_checks": proof_certificates,
        "degree_table": degree_table,
        "claim_boundary": (
            "Exact finite linear algebra through the declared degree cutoff; "
            "it does not prove cyclicity over the untruncated polynomial ring."
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--degree", type=int, default=12)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("experiments/divided_cube_graded_orbit_result.json"),
    )
    args = parser.parse_args()
    result = analyze(args.degree)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result))
    assert result["all_distinct_generates_projected_kernel"]


if __name__ == "__main__":
    main()
