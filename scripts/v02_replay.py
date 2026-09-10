#!/usr/bin/env python3
"""Exact synthetic controls for v0.2. No curve attacks or unknown secrets.

Only finite observations and integer/rational arithmetic are tested. These
checks never assert Lean verification or a universal ECDLP complexity theorem.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
from math import factorial
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'release_candidates/v0.2/replay.json'
N = 115792089237316195423570985008687907852837564279074904382605163141518161494337


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def negation_pairs(n: int) -> dict[str, int]:
    require(n >= 3 and n % 2 == 1, 'n must be odd and at least 3')
    # The feature is the unordered sign pair, not a computable secp256k1 oracle.
    fibers: dict[int, list[int]] = {}
    for k in range(1, n):
        key = min(k, n-k)
        counts = fibers.setdefault(key, [0, 0])
        counts[k % 2] += 1
    require(all(c == [1, 1] for c in fibers.values()), 'unbalanced sign pair')
    optimum = sum(max(c) for c in fibers.values())
    require(2 * optimum == n-1, 'sign-pair ceiling is not exactly one half')
    return {'order': n, 'observations': n-1, 'optimal_correct': optimum}


def local_control(m: int) -> dict[str, int | bool]:
    require(m >= 1, 'm must be positive')
    n = 4*m + 1
    truth = [k % 2 for k in range(n)]
    predicted = [truth[k] ^ int(m+1 <= k <= 3*m) for k in range(n)]
    correct = sum(predicted[k] == truth[k] for k in range(1, n))
    negation = sum(predicted[k] != predicted[n-k] for k in range(1, n))
    # Ordinary adjacent edges exclude only the exceptional wraparound edge.
    edges = sum(predicted[k] != predicted[k+1] for k in range(n-1))
    anchors = all(predicted[k] == truth[k] for k in (0, 1, n-1))
    wrap = predicted[n-1] == predicted[0]
    require(correct == 2*m, 'global accuracy changed')
    require(negation == n-1 and edges == n-3 and anchors and wrap,
            'local-control contract failed')
    return {'order': n, 'nonzero_observations': n-1, 'correct': correct,
            'ordinary_edges': n-1, 'ordinary_edges_satisfied': edges,
            'negation_checks_satisfied': negation, 'anchors_correct': anchors,
            'wraparound_correct': wrap}


def evaluate() -> dict:
    pairs = [negation_pairs(n) for n in range(3, 258, 2)]
    controls = [local_control(m) for m in range(1, 65)]
    large = local_control(16384)
    t = Fraction(89, 128)
    exp_lower = sum((t ** j) / factorial(j) for j in range(6))
    require(exp_lower > 2, 'exponential lower polynomial is not above two')
    numerator = 17*179*2**128*10**36
    denominator = 9*(N-1)
    require(numerator < denominator, 'rational envelope comparison failed')
    require(N < 2**256 and 17**2 > 32*3**2, 'auxiliary numerical inequalities failed')
    # These are arithmetic facts. Analytic monotonicity, character sums,
    # subgroup index, and an applicability theorem are separate obligations.
    return {
        'schema_version': 1,
        'scope': 'synthetic finite scalar controls and exact arithmetic only',
        'lean_status': 'not_run',
        'negation_pair_controls': {'odd_orders': len(pairs),
            'observations': sum(r['observations'] for r in pairs), 'all_balanced': True},
        'local_control_family': {'instances': len(controls), 'm_min': 1, 'm_max': 64,
            'all_contracts_satisfied': True},
        'large_local_control': large,
        'rational_envelope': {'order_parameter': str(N),
            'comparison': '17*179*2^128*10^36 < 9*(n-1)',
            'left': str(numerator), 'right': str(denominator), 'holds': True,
            'exponential_lower_sum': {'numerator': str(exp_lower.numerator),
                                      'denominator': str(exp_lower.denominator)},
            'analytic_cycle_bound_formalized': False,
            'multiplicative_order_reverified': False},
        'literature_novelty_established': False,
        'production_keys_used': False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='compare, without changing the frozen result')
    args = parser.parse_args()
    try:
        report = evaluate()
        text = json.dumps(report, indent=2, sort_keys=True) + '\n'
        if args.check:
            require(OUTPUT.is_file() and OUTPUT.read_text(encoding='utf-8') == text,
                    'frozen replay is missing or has drifted')
        else:
            OUTPUT.parent.mkdir(parents=True, exist_ok=True)
            OUTPUT.write_text(text, encoding='utf-8')
        print(text, end='')
        return 0
    except (ValueError, OSError) as exc:
        print(f'REPLAY FAILED: {exc}')
        return 1

if __name__ == '__main__':
    raise SystemExit(main())
