# Theta screen 002

This directory contains a bounded structural and solver screen for the theta
route. It is not an ECDLP attack experiment, does not target a real key, and
does not authorize route promotion.

## Questions

1. Does the split 2-torsion Kummer coordinate create a new `C3` symmetry when
   combined with secp256k1 GLV?
2. Can a full-point Jacobi extended formulation exploit lower factor-base
   degree strongly enough to compensate for its additional variables?
3. Does a p-adic canonical lift place prime-to-p secp256k1 torsion in the
   formal neighborhood where a formal logarithm could linearize it?

The current answers are:

- the split Kummer `C3` is the same action as inverse Frobenius and GLV;
- after shifting its fixed point, its cubic invariant is a nonzero scalar
  multiple of `x^3`;
- full-point Jacobi systems are slower in the current SymPy toy screen;
- Jacobi factor-base degree compression remains a bounded Singular question;
- the formal group has no nonzero n-torsion when `p` does not divide `n`, so
  the direct p-adic formal-log interpretation is blocked.

See `notes/THETA_SCREEN_002.md` for the derivations and claim boundaries.

## Exact secp256k1 structural verification

Using SageMath:

```bash
sage -python experiments/theta_screen_002/verify_secp.py
```

The script checks the exact secp256k1 field and writes
`verify_secp_result.json`.

## Singular factor-base screen

One example:

```bash
sage -python experiments/theta_screen_002/singular_factorbase.py \
  --h 2 \
  --system projective \
  --order degrevlex \
  --layout intermediate_first \
  --timeout 180 \
  --out experiments/theta_screen_002/results/h2_projective.json
```

Here `h` is the number of allowed values of `s^2`. The corresponding
Weierstrass factor base contains `4h` x-values. The direct system therefore has
factor polynomials of degree `4h`, while the Jacobi representation uses degree
`2h` polynomials in `s`.

The supported projective variable layouts are:

- `coordinate`
- `point`
- `intermediate_first`

No single final Groebner degree is accepted as success. Compare total time,
peak memory, basis size, input size, timeouts, and scaling across `h`.

## Official Docker image

On Windows with Docker Desktop or WSL:

```powershell
docker pull sagemath/sagemath:10.9
docker run --rm -v "${PWD}:/work" -w /work sagemath/sagemath:10.9 `
  sage -python experiments/theta_screen_002/verify_secp.py
```

The convenience launcher `run_sage.ps1` runs the bounded matrix of cases and
creates `sage_results.zip`.

## Required interpretation

A positive toy result is at most `supported`. It is not evidence of a
sub-Pollard algorithm without a mechanism and scaling theorem. A negative toy
result is scoped to this representation and solver configuration. All exact
secp256k1 DLP targets remain forbidden by the current decision substrate.
