# SPDX-License-Identifier: Apache-2.0
"""Exact support checks over small prime fields. No discrete-log search.

Coefficients are in ascending order. Public entry points validate the domain.
The prime check is intentionally limited to small verification examples, not a
primality certificate for secp256k1. Written during AI-assisted evidence intake.
"""
from __future__ import annotations

from math import isqrt

Poly = list[int]


def trim(a: Poly, p: int) -> Poly:
    out = [int(x) % p for x in a] or [0]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def add(a: Poly, b: Poly, p: int) -> Poly:
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return trim(out, p)


def mul(a: Poly, b: Poly, p: int) -> Poly:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(out, p)


def divmod_poly(a: Poly, b: Poly, p: int) -> tuple[Poly, Poly]:
    a, b = trim(a, p), trim(b, p)
    if b == [0]:
        raise ValueError('zero polynomial divisor')
    out = [0] * max(1, len(a) - len(b) + 1)
    inv = pow(b[-1], -1, p)
    while a != [0] and len(a) >= len(b):
        k = len(a) - len(b)
        c = a[-1] * inv % p
        out[k] = c
        for j, x in enumerate(b):
            a[k + j] = (a[k + j] - c * x) % p
        a = trim(a, p)
    return trim(out, p), a


def remainder(a: Poly, g: Poly, p: int) -> Poly:
    return divmod_poly(a, g, p)[1]


def power_mod(a: Poly, e: int, g: Poly, p: int) -> Poly:
    if e < 0:
        raise ValueError('negative exponent')
    out, a = [1], remainder(a, g, p)
    while e:
        if e & 1:
            out = remainder(mul(out, a, p), g, p)
        e //= 2
        if e:
            a = remainder(mul(a, a, p), g, p)
    return out


def derivative(a: Poly, p: int) -> Poly:
    return trim([i * a[i] for i in range(1, len(a))], p)


def evaluate(a: Poly, x: int, p: int) -> int:
    out = 0
    for c in reversed(a):
        out = (out * x + c) % p
    return out


def validate(g: Poly, f: Poly, p: int) -> tuple[Poly, Poly, int]:
    if type(p) is not int or p < 2 or p > 10000:
        raise ValueError('verification prime must be an integer in [2,10000]')
    if any(p % d == 0 for d in range(2, isqrt(p) + 1)):
        raise ValueError('field modulus must be prime')
    for a in (g, f):
        if not isinstance(a, list) or not a or any(type(x) is not int for x in a):
            raise ValueError('polynomials must be nonempty integer lists')
    g, f = trim(g, p), trim(f, p)
    q = len(g) - 1
    if not 0 < q < p or g[-1] != 1:
        raise ValueError('g must be monic with 0 < degree(g) < p')
    return g, f, q


def supported(g: Poly, f: Poly, p: int) -> bool:
    g, f, _ = validate(g, f, p)
    return remainder(mul(f, derivative(g, p), p), g, p) == [0]


def jacobian(g: Poly, f: Poly, p: int) -> list[list[int]]:
    """Jacobian of rem(f*g',g) at a solution; f is held fixed.

    No full-rank claim is made unless f is squarefree on the support.
    """
    g, f, q = validate(g, f, p)
    quotient, rem = divmod_poly(mul(f, derivative(g, p), p), g, p)
    if rem != [0]:
        raise ValueError('Jacobian shortcut is valid only at a solution')
    columns = []
    for i in range(q):
        h = [0] * i + [1]
        a = mul(f, derivative(h, p), p)
        b = [-x for x in mul(quotient, h, p)]
        column = remainder(add(a, b, p), g, p)
        columns.append(column + [0] * (q - len(column)))
    return [[columns[j][i] for j in range(q)] for i in range(q)]


def determinant(matrix: list[list[int]], p: int) -> int:
    q = len(matrix)
    if any(len(row) != q for row in matrix):
        raise ValueError('square matrix required')
    a = [[x % p for x in row] for row in matrix]
    out = 1
    for i in range(q):
        pivot = next((j for j in range(i, q) if a[j][i]), None)
        if pivot is None:
            return 0
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            out = -out
        out = out * a[i][i] % p
        inv = pow(a[i][i], -1, p)
        for j in range(i + 1, q):
            c = a[j][i] * inv % p
            for k in range(i, q):
                a[j][k] = (a[j][k] - c * a[i][k]) % p
    return out % p
