#!/usr/bin/env python3
"""Replay the exact C56 reduction from a tau_3 shift oracle to ECDLP.

The oracle is simulated from the hidden scalar only for validation. The recovery
algorithm itself receives one bit per adaptively shifted subgroup point and
maintains a cyclic candidate interval until a singleton remains.
"""

from __future__ import annotations

import argparse
import json
import random
from pathlib import Path
from typing import Any, Callable

SECP_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


def is_prime_trial(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    divisor = 3
    while divisor * divisor <= n:
        if n % divisor == 0:
            return False
        divisor += 2
    return True


def middle_third_interval(n: int) -> tuple[int, int]:
    """Return (start, length) for floor(3*k/n)=1 in canonical residues."""
    if n <= 3 or n % 2 == 0 or n % 3 == 0:
        raise ValueError("n must be odd, greater than 3, and coprime to 3")
    start = (n + 2) // 3
    end = (2 * n + 2) // 3 - 1
    return start, end - start + 1


def tau3_negative_bit(residue: int, n: int) -> int:
    """Return 1 exactly when tau_3(residue)=-1."""
    residue %= n
    return (3 * residue // n) & 1


def recover_from_tau3_shift_oracle(
    n: int,
    query_shift: Callable[[int], int],
) -> tuple[int, int]:
    """Recover k using queries for tau_3([k+t]_n), where t is public.

    `query_shift(t)` must return 1 exactly when tau_3([k+t]_n)=-1.
    The result is `(k, number_of_queries)`.
    """
    interval_start, interval_length = middle_third_interval(n)
    s = interval_length

    def query_interval_start(start: int) -> int:
        # I_n - t begins at `start` exactly when t=I_start-start.
        shift = (interval_start - start) % n
        bit = query_shift(shift)
        if bit not in (0, 1):
            raise ValueError("oracle must return a bit")
        return bit

    queries = 1
    if query_interval_start(interval_start):
        candidate_start = interval_start
        candidate_length = s
    else:
        candidate_start = (interval_start + s) % n
        candidate_length = n - s

    while candidate_length > 1:
        prefix_length = candidate_length // 2

        # The translated interval has length s. Its suffix of length
        # prefix_length coincides with the candidate prefix; the remaining
        # s-prefix_length points lie in the known complement immediately before
        # the candidate interval.
        query_start = (candidate_start - (s - prefix_length)) % n

        if query_interval_start(query_start):
            candidate_length = prefix_length
        else:
            candidate_start = (candidate_start + prefix_length) % n
            candidate_length -= prefix_length
        queries += 1

    return candidate_start, queries


def simulated_oracle(hidden_scalar: int, n: int) -> Callable[[int], int]:
    hidden_scalar %= n

    def query(shift: int) -> int:
        return tau3_negative_bit(hidden_scalar + shift, n)

    return query


def ceil_log2(value: int) -> int:
    if value <= 0:
        raise ValueError("value must be positive")
    return (value - 1).bit_length()


def replay(random_checks: int, small_prime_limit: int) -> dict[str, Any]:
    n = SECP_N
    interval_start, interval_length = middle_third_interval(n)
    worst_initial_length = n - interval_length
    query_bound = 1 + ceil_log2(worst_initial_length)
    assert query_bound == 257

    rng = random.Random(0xC5603)
    secp_max_queries = 0
    for _ in range(random_checks):
        hidden = rng.randrange(n)
        recovered, queries = recover_from_tau3_shift_oracle(
            n, simulated_oracle(hidden, n)
        )
        assert recovered == hidden
        assert queries <= query_bound
        secp_max_queries = max(secp_max_queries, queries)

    prime_orders = 0
    exhaustive_scalar_cases = 0
    small_max_queries = 0
    for order in range(5, small_prime_limit + 1, 2):
        if not is_prime_trial(order) or order == 3:
            continue
        prime_orders += 1
        start, length = middle_third_interval(order)
        local_bound = 1 + ceil_log2(order - length)
        assert start == (order + 2) // 3

        for hidden in range(order):
            recovered, queries = recover_from_tau3_shift_oracle(
                order, simulated_oracle(hidden, order)
            )
            assert recovered == hidden
            assert queries <= local_bound
            exhaustive_scalar_cases += 1
            small_max_queries = max(small_max_queries, queries)

    return {
        "schema": "uorc056.tau3_shift_reduction.certificate.v1",
        "curve": "secp256k1",
        "subgroup_order_n": str(n),
        "middle_third_start": str(interval_start),
        "middle_third_length": str(interval_length),
        "worst_initial_candidate_length": str(worst_initial_length),
        "exact_query_bound": query_bound,
        "random_secp256k1_scalars_checked": random_checks,
        "maximum_queries_observed_on_secp256k1": secp_max_queries,
        "small_prime_limit": small_prime_limit,
        "small_prime_orders_checked": prime_orders,
        "exhaustive_small_scalar_cases": exhaustive_scalar_cases,
        "maximum_queries_observed_on_small_orders": small_max_queries,
        "reduction": (
            "A uniform exact evaluator for tau_3([r]G) on adaptively shifted "
            "points Q+[t]G recovers the canonical discrete logarithm."
        ),
        "claims_not_made": [
            "No evaluator for tau_3 is constructed.",
            "No unconditional per-query time lower bound is proved.",
            "No sub-square-root ECDLP algorithm is constructed.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--random-checks", type=int, default=10_000)
    parser.add_argument("--small-prime-limit", type=int, default=5_000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    if args.random_checks < 0 or args.small_prime_limit < 5:
        parser.error("invalid replay limits")

    certificate = replay(args.random_checks, args.small_prime_limit)
    rendered = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
