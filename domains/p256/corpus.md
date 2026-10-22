# P-256 domain corpus (atomic claims + status)

Starter claim corpus for the **NIST P-256 / secp256r1** domain — the second live instance of
the Research OS. Small and honest: each claim is either **verified** (a kernel-checked row in
the top-level `VERIFIED.md`, referencing an `Ecdlp/Proved/P256*.lean` file) or **planned** (a
rung the same secp256k1 machinery reaches but which is not built yet). No claim is asserted
before the Lean kernel accepts it.

Provenance: FIPS 186-4 / SEC 2 domain parameters; the same generators and proof patterns as
secp256k1 (`scripts/pratt_certificate.py`, `Ecdlp/Proved/Secp256k1*.lean`).

| id | claim | status | evidence |
|---|---|---|---|
| p256-field-prime | the field prime `p = 2²⁵⁶−2²²⁴+2¹⁹²+2⁹⁶−1` is prime | **verified** | `Ecdlp/Proved/P256PrimeP.lean` (`p256_p_prime`) |
| p256-order-prime | the group order `n` is prime | **verified** | `Ecdlp/Proved/P256PrimeN.lean` (`p256_n_prime`) |
| p256-elliptic-curve | `y² = x³ − 3x + b` is a nonsingular `EllipticCurve` over `𝔽_p` (unconditional, given the primality above) | **verified** | `Ecdlp/Proved/P256Curve.lean` (`P256_Δ_ne_zero` + `IsElliptic`) |
| p256-base-point | the SEC 2 generator `G = (Gx, Gy)` is a rational point of the curve | **verified** | `Ecdlp/Proved/P256Curve.lean` (`P256_generator_equation`) |
| p256-no-glv | `c₄ ≠ 0`, hence `j ≠ 0`: P-256 has no CM / GLV endomorphism (structural contrast with secp256k1) | **verified** | `Ecdlp/Proved/P256Curve.lean` (`P256_c₄_ne_zero`) |
| p256-generator-order | the base point `G` has order exactly `n` (prime-order group; weak keystone, no `#E`) | **verified** | `Ecdlp/Proved/P256GeneratorOrder.lean` (`p256_generator_addOrderOf`) |
| p256-embedding-degree | large embedding degree (`> 100`) — MOV/Frey–Rück resistance | **verified** | `Ecdlp/Proved/P256EmbeddingDegree.lean` (`p256_embedding_degree_gt_100`) |
| p256-non-anomalous | ordinary, non-anomalous (`t≠1`), Hasse-consistent — Smart/SSSA resistance (given `#E=n`, see `p256-exact-cardinality`) | **verified** | `Ecdlp/Proved/P256TraceOfFrobenius.lean` (`p256_trace_ordinary_nonanomalous`) |
| p256-generic-bound | generic-group `Ω(√n)` hardness core applies | **verified** | curve-agnostic: `Ecdlp/Proved/GenericGroupBound.lean` (`generic_dlog_query_bound`, stated for any prime — applies to P-256's `n` with no new proof) |
| p256-exact-cardinality | exact point count `#E(𝔽_p) = n` (cofactor 1), without the Hasse bound or a point-counting algorithm; inherits `native_decide` trust from `n•G = 0` and the Pratt certificates; prior art: pyca/verified-garbage proves `#E = n` for its own specification curve type | **verified** | `Ecdlp/Proved/P256CardinalityExact.lean` (`p256_card_point_eq_n`), via `Ecdlp/Proved/PrimeOrderCardinality.lean` and `Ecdlp/Proved/CubicNoRootCertificate.lean` |
