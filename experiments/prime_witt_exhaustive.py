#!/usr/bin/env python3
"""Exhaust length-two p-typical Witt carry identities over prime fields."""

from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path

State = tuple[int, int]


def carry(p: int, a: int, c: int) -> int:
    """The integral Witt polynomial (X^p+Y^p-(X+Y)^p)/p modulo p."""
    coefficients = [math.comb(p, k) // p for k in range(1, p)]
    assert all(math.comb(p, k) % p == 0 for k in range(1, p))
    return -sum(
        coefficient * pow(a, k) * pow(c, p - k)
        for k, coefficient in enumerate(coefficients, start=1)
    ) % p


def add(p: int, x: State, y: State) -> State:
    a, b = x
    c, d = y
    return ((a + c) % p, (b + d + carry(p, a, c)) % p)


def scalar_mul(p: int, multiplicity: int, x: State) -> State:
    result = (0, 0)
    for _ in range(multiplicity):
        result = add(p, result, x)
    return result


def teichmueller_index(p: int, x: State) -> int:
    a, b = x
    return (pow(a, p, p * p) + p * b) % (p * p)


def verify_prime(p: int) -> dict[str, object]:
    assert p >= 2
    assert all(p % divisor for divisor in range(2, math.isqrt(p) + 1))
    states = list(itertools.product(range(p), repeat=2))

    normalization = all(carry(p, 0, a) == 0 and carry(p, a, 0) == 0 for a in range(p))
    symmetry = all(carry(p, a, c) == carry(p, c, a)
                   for a, c in itertools.product(range(p), repeat=2))
    cocycle = all(
        (carry(p, a, b) + carry(p, (a + b) % p, c)) % p
        == (carry(p, b, c) + carry(p, a, (b + c) % p)) % p
        for a, b, c in itertools.product(range(p), repeat=3)
    )
    associativity = all(
        add(p, add(p, x, y), z) == add(p, x, add(p, y, z))
        for x, y, z in itertools.product(states, repeat=3)
    )
    teichmueller_additivity = all(
        teichmueller_index(p, add(p, x, y))
        == (teichmueller_index(p, x) + teichmueller_index(p, y)) % (p * p)
        for x, y in itertools.product(states, repeat=2)
    )
    teichmueller_bijective = len({teichmueller_index(p, x) for x in states}) == p * p
    multiplication_by_p = all(scalar_mul(p, p, (a, b)) == (0, a)
                              for a, b in states)

    orbit: list[State] = []
    current = (0, 0)
    for _ in range(p * p):
        orbit.append(current)
        current = add(p, current, (1, 0))
    generator_order_p_squared = current == (0, 0) and len(set(orbit)) == p * p

    checks = {
        "normalized": normalization,
        "symmetric": symmetry,
        "cocycle": cocycle,
        "associative": associativity,
        "teichmueller_additive": teichmueller_additivity,
        "teichmueller_bijective": teichmueller_bijective,
        "multiplication_by_p_is_0_a": multiplication_by_p,
        "generator_order_p_squared": generator_order_p_squared,
    }
    assert all(checks.values())
    return {
        "prime": p,
        "state_count": len(states),
        "ordered_pair_count": len(states) ** 2,
        "ordered_triple_count": len(states) ** 3,
        "carry_coefficients": [
            (-math.comb(p, k) // p) % p for k in range(1, p)
        ],
        "teichmueller_formula": f"phi(a,b) = a^{p} + {p}b mod {p*p}",
        "checks": checks,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", type=int, nargs="+", default=[3, 5, 7])
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).with_name("prime_witt_exhaustive_result.json"),
    )
    args = parser.parse_args()
    results = [verify_prime(p) for p in args.primes]
    payload = {
        "status": "passed",
        "results": results,
        "claim_boundary": (
            "Exhaustive scalar identities over the listed prime fields; functional carry "
            "naturality and the infinite module construction remain paper/formal proof obligations."
        ),
    }
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, sort_keys=True))


if __name__ == "__main__":
    main()
