#!/usr/bin/env python3
"""Replay certificate for UORC-056 C56 cross-cycle carry bounds.

The script is deliberately dependency-free. It verifies the exact scalar
identities, quotient-cycle actions for multipliers 3 and 5, carry biases, and
the integer arithmetic behind the character-sum degree lower bounds.

It does not prove the external character-sum theorem. The note cites
Shparlinski-Stange, Lemma 5, for that analytic input.
"""

from __future__ import annotations

import argparse
import json
import random
from math import isqrt
from pathlib import Path
from typing import Any

SECP_P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
SECP_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
DOUBLING_INDEX = 64
DOUBLING_ORDER = (SECP_N - 1) // DOUBLING_INDEX


def sign_from_bit(bit: int) -> int:
    return -1 if bit & 1 else 1


def scalar_parity_sign(k: int, n: int) -> int:
    """Return (-1)^[k]_n for the canonical residue in [0,n)."""
    return sign_from_bit((k % n) & 1)


def carry_sign(a: int, k: int, n: int) -> int:
    """Return (-1)^floor(a*k/n), with 0 <= k < n and odd a."""
    if a <= 0 or a % 2 == 0:
        raise ValueError("a must be a positive odd integer")
    if not 0 <= k < n:
        raise ValueError("k must be canonical: 0 <= k < n")
    return sign_from_bit((a * k) // n)


def transport_sign(a: int, k: int, n: int) -> int:
    """Return sigma([a*k]_n) / sigma(k), represented in {+1,-1}."""
    return scalar_parity_sign(a * k, n) * scalar_parity_sign(k, n)


def carry_block_count(n: int, a: int, q: int) -> int:
    """Count k in 1..n-1 with floor(a*k/n)=q."""
    if not (0 <= q < a):
        raise ValueError("q must satisfy 0 <= q < a")
    return (((q + 1) * n - 1) // a) - ((q * n) // a)


def carry_bias(n: int, a: int) -> int:
    """Compute sum_{k=1}^{n-1} (-1)^floor(a*k/n) from block counts."""
    return sum(sign_from_bit(q) * carry_block_count(n, a, q) for q in range(a))


def order_in_power_of_two_group(z: int, modulus: int, upper_order: int) -> int:
    """Return the exact order of z, assuming it divides upper_order=2^t."""
    if upper_order <= 0 or upper_order & (upper_order - 1):
        raise ValueError("upper_order must be a power of two")
    if pow(z, upper_order, modulus) != 1:
        raise AssertionError("element order does not divide upper_order")
    order = upper_order
    while order > 1 and pow(z, order // 2, modulus) == 1:
        order //= 2
    return order


def ceil_x_over_2_sqrt_p(x: int, p: int) -> int:
    """Exact ceil(x/(2*sqrt(p))) using integer comparisons only."""
    if x <= 0 or p <= 0:
        raise ValueError("x and p must be positive")
    denominator_square = 4 * p
    candidate = isqrt((x * x) // denominator_square)
    while candidate * candidate * denominator_square < x * x:
        candidate += 1
    while candidate > 0 and (candidate - 1) ** 2 * denominator_square >= x * x:
        candidate -= 1
    return candidate


def is_prime_trial(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def replay(random_checks: int, small_prime_limit: int) -> dict[str, Any]:
    p = SECP_P
    n = SECP_N
    m = DOUBLING_ORDER

    assert n % 2 == 1
    assert m * DOUBLING_INDEX == n - 1
    assert m % 2 == 1
    assert pow(2, m, n) == 1

    multipliers: dict[str, Any] = {}
    for a in (3, 5):
        label = pow(a, m, n)
        quotient_order = order_in_power_of_two_group(label, n, DOUBLING_INDEX)
        bias = carry_bias(n, a)
        degree_bound = ceil_x_over_2_sqrt_p(abs(bias) - 1, p)
        multipliers[str(a)] = {
            "cycle_label_multiplier": str(label),
            "cycle_label_multiplier_order": quotient_order,
            "crosses_doubling_cycles": label != 1,
            "carry_bias_nonzero_scalars": str(bias),
            "character_degree_lower_bound": str(degree_bound),
            "character_degree_lower_bound_bits": degree_bound.bit_length(),
        }

    assert multipliers["3"]["cycle_label_multiplier_order"] == 32
    assert multipliers["5"]["cycle_label_multiplier_order"] == 64
    assert carry_bias(n, 3) == (n - 1) // 3

    rng = random.Random(0xC56)
    for _ in range(random_checks):
        k = rng.randrange(0, n)
        for a in (3, 5):
            assert transport_sign(a, k, n) == carry_sign(a, k, n)

        a = rng.choice((3, 5, 7, 9, 11))
        b = rng.choice((3, 5, 7, 9, 11))
        left = carry_sign(a * b, k, n)
        bk = (b * k) % n
        right = carry_sign(a, bk, n) * carry_sign(b, k, n)
        assert left == right

    checked_small_primes = 0
    for modulus in range(3, small_prime_limit + 1, 2):
        if not is_prime_trial(modulus):
            continue
        checked_small_primes += 1
        for a in (3, 5, 7):
            if a >= modulus or modulus % a == 0:
                continue
            direct_bias = 0
            for k in range(1, modulus):
                assert transport_sign(a, k, modulus) == carry_sign(a, k, modulus)
                direct_bias += carry_sign(a, k, modulus)
            assert direct_bias == carry_bias(modulus, a)

    return {
        "schema": "uorc056.cross_cycle_carry.certificate.v1",
        "curve": "secp256k1",
        "field_prime_p": str(p),
        "subgroup_order_n": str(n),
        "doubling_index": DOUBLING_INDEX,
        "doubling_order_M": str(m),
        "doubling_order_bits": m.bit_length(),
        "multipliers": multipliers,
        "exact_rational_value_degree_lower_bound": str((n - 1) // 2),
        "exact_rational_value_degree_lower_bound_bits": ((n - 1) // 2).bit_length(),
        "random_transport_and_cocycle_checks": random_checks,
        "small_prime_exhaustive_limit": small_prime_limit,
        "small_primes_checked": checked_small_primes,
        "external_theorem_dependency": {
            "paper": "Shparlinski-Stange, Character Sums with Division Polynomials",
            "result": "Lemma 5",
            "arxiv": "0912.5246v4",
            "use": "|sum_{P in H} chi(f(P))| <= 2*deg(f)*sqrt(p) under the Kummer non-power hypothesis",
        },
        "claims_not_made": [
            "No parity oracle is constructed.",
            "No circuit-size lower bound follows from the degree lower bound.",
            "High-degree low-circuit and non-character transports remain open.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--random-checks", type=int, default=10_000)
    parser.add_argument("--small-prime-limit", type=int, default=5_000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    if args.random_checks < 0 or args.small_prime_limit < 3:
        parser.error("invalid replay limits")

    certificate = replay(args.random_checks, args.small_prime_limit)
    rendered = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
