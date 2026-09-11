#!/usr/bin/env python3
"""Exact secp256k1 M16 factor-base count, using Python's standard library.

This is a deterministic finite arithmetic check, not an ECDLP solver,
a performance result, or a Lean proof. It assumes the standard secp256k1
field modulus is prime. No secret keys, network access, or third-party
packages are used. Both checks must agree.
"""
import json
from time import perf_counter

P = 2**256 - 2**32 - 977
D = 2 * 3 * 7 * 13441
EXPECTED = {
    "cube_positive": 94509,
    "cube_negative": 93665,
    "cube_zero": 0,
    "usable_x": 283527,
    "non_lifting_x": 280995,
    "zero_y_x": 0,
    "character_sum": 2532,
    "signed_points": 567054,
    "glv_and_sign_classes": 94509,
}

def jacobi(a: int, n: int) -> int:
    if n <= 0 or n % 2 == 0:
        raise ValueError("The denominator must be positive and odd.")
    a %= n
    sign = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                sign = -sign
        a, n = n, a
        if a % 4 == n % 4 == 3:
            sign = -sign
        a %= n
    return sign if n == 1 else 0

def subgroup_generator() -> int:
    if (P - 1) % D:
        raise RuntimeError("D does not divide P-1")
    h = pow(3, (P - 1) // D, P)
    if pow(h, D, P) != 1:
        raise RuntimeError("Invalid subgroup generator")
    if any(pow(h, D // r, P) == 1 for r in (2, 3, 7, 13441)):
        raise RuntimeError("The generator has order smaller than D")
    return h

def check_via_cube_image_and_euler(h: int) -> dict:
    step = pow(h, 3, P)
    u = 1
    counts = {1: 0, -1: 0, 0: 0}
    for _ in range(D // 3):
        value = pow((u + 7) % P, (P - 1) // 2, P)
        if value == 1:
            chi = 1
        elif value == P - 1:
            chi = -1
        elif value == 0:
            chi = 0
        else:
            raise RuntimeError("Unexpected Euler-criterion value")
        counts[chi] += 1
        u = u * step % P
    if u != 1:
        raise RuntimeError("Cube-image traversal did not close")
    return counts

def check_full_subgroup_via_reciprocity(h: int) -> dict:
    step = pow(h, -1, P)
    x = 1
    counts = {1: 0, -1: 0, 0: 0}
    for _ in range(D):
        rhs = (x * x % P * x + 7) % P
        counts[jacobi(rhs, P)] += 1
        x = x * step % P
    if x != 1:
        raise RuntimeError("Full-subgroup traversal did not close")
    return counts

def main() -> None:
    h = subgroup_generator()
    start = perf_counter()
    cube = check_via_cube_image_and_euler(h)
    t_euler = perf_counter() - start
    start = perf_counter()
    full = check_full_subgroup_via_reciprocity(h)
    t_jacobi = perf_counter() - start
    if any(full[c] != 3 * cube[c] for c in (-1, 0, 1)):
        raise RuntimeError("The independent arithmetic checks disagree")
    if full[0] != 0:
        raise RuntimeError("Unexpected zero-y point; orbit formula needs adjustment")
    result = {
        "cube_positive": cube[1],
        "cube_negative": cube[-1],
        "cube_zero": cube[0],
        "usable_x": full[1] + full[0],
        "non_lifting_x": full[-1],
        "zero_y_x": full[0],
        "character_sum": full[1] - full[-1],
        "signed_points": 2 * full[1] + full[0],
        "glv_and_sign_classes": full[1] // 3,
    }
    if result != EXPECTED:
        raise RuntimeError(f"Unexpected counts: {result!r}")
    print(json.dumps({
        "status": "PASS_TWO_ARITHMETIC_METHODS",
        "field_prime": str(P),
        "subgroup_order": D,
        "subgroup_generator": str(h),
        "counts": result,
        "runtime_seconds": {"euler_cube": t_euler, "jacobi_full": t_jacobi},
        "not_claimed": [
            "formal Lean verification", "global mathematical novelty",
            "relation-generation success probability", "relation rank",
            "solving degree", "sub-square-root ECDLP algorithm"
        ],
    }, indent=2))

if __name__ == "__main__":
    main()
