# SPDX-License-Identifier: Apache-2.0
"""Deterministic small-field replay; stdout JSON, no network or API keys.

This checks a polynomial lemma, not the global M16 search, Lean, or novelty.
Run: python3 release_candidates/m16-20260910/replay.py
"""
from __future__ import annotations

import itertools
import json
import math
from support import (derivative, determinant, divmod_poly, evaluate, jacobian,
                     mul, power_mod, remainder, supported)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def linear_support(g: list[int], roots: list[int], p: int):
    """Alternative support check by division, not the derivative identity."""
    rest, multiplicities = list(g), {}
    for root in roots:
        count = 0
        while len(rest) > 1:
            quotient, rem = divmod_poly(rest, [-root, 1], p)
            if rem != [0]:
                break
            rest, count = quotient, count + 1
        if count:
            multiplicities[root] = count
    return len(rest) == 1, multiplicities


def run() -> dict:
    cases = []
    for p, maxq, roots in ((5, 4, [1, 2]), (7, 4, [0, 1, 3]), (11, 3, [2, 5])):
        f = [1]
        for root in roots:
            f = mul(f, [-root, 1], p)
        checked = positive = 0
        for q in range(1, maxq + 1):
            for coefficients in itertools.product(range(p), repeat=q):
                g = list(coefficients) + [1]
                accepted = supported(g, f, p)
                oracle, multiplicities = linear_support(g, roots, p)
                powered = power_mod(f, q, g, p) == [0]
                require(accepted == oracle == powered, 'support disagreement')
                if accepted:
                    det = determinant(jacobian(g, f, p), p)
                    expected = (-1) ** q
                    for root, e in multiplicities.items():
                        expected *= math.factorial(e) * pow(evaluate(derivative(f, p), root, p), e, p)
                    require(det != 0 and det == expected % p, 'determinant disagreement')
                    positive += 1
                checked += 1
        cases.append({'p': p, 'max_q': maxq, 'roots': roots,
                      'polynomials': checked, 'supported_full_rank': positive})
    # Deliberately bypass the public guard to demonstrate why p > q matters.
    g, f, p = [0, 0, 0, 1], [-1, 1], 3
    require(remainder(mul(f, derivative(g, p), p), g, p) == [0], 'counterexample derivative')
    require(power_mod(f, 3, g, p) != [0], 'counterexample power')
    try:
        supported(g, f, p)
    except ValueError:
        pass
    else:
        raise RuntimeError('characteristic guard failed')
    require(sum(r['polynomials'] for r in cases) == 5043, 'case count')
    require(sum(r['supported_full_rank'] for r in cases) == 57, 'positive count')
    return {'schema': 'm16-support-replay/v1', 'status': 'PASS', 'cases': cases,
            'polynomials_checked': 5043, 'full_rank_cases': 57,
            'characteristic_counterexample_rejected': True,
            'lean_checked': False, 'new_target_secp256k1_solutions': 0,
            'independence': 'Alternative algebraic checks share arithmetic and authorship; not external review.'}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
