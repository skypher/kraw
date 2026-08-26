# Certificate map

This file maps every computer-assisted statement in the manuscript to its
exact generator, committed replay log, and logical obligations. The `.txt`
files are deterministic execution records; the corresponding source is the
generative certificate and must be inspected or replayed.

For a function-by-function inspection route and the acceptance predicate of
each verifier, see `certificates/REVIEW_CHECKLIST.md`.

No floating-point diagnostic discharges a proof obligation. All accepted
symbolic identities, coefficient signs, Sturm counts, resultants, recurrence
values, and coverage censuses use exact integer or rational arithmetic.
The primary generators trust the declared SymPy implementations of polynomial
factorization, gcd, resultant, and Sturm root counting.  The independently
implemented checks in `INDEPENDENT_CHECKS.md` replay the decisive outputs
without those operations or GMP.

## Core identities and finite scan

| Manuscript result | Generator | Exact log | Obligations |
|---|---|---|---|
| Recurrence and Lemma 2.1 | `scripts/recurrence-and-small-scan.py` | `certificates/recurrence-and-small-scan.txt` | Coefficient recurrence against the binomial definition; direct exact scan for `M,Q <= 90`. |
| Proposition 2.2 | `cpp/exhaustive-turan-scan.cpp`; `cpp/independent-pascal-scan.cpp` | `certificates/exhaustive-scan-D1200.txt`; `certificates/independent-scan-D1200.txt` | The primary GMP recurrence scan performs all prior structural checks. The second scan independently constructs every row from both Pascal parents with Boost integers, checks their coefficientwise agreement, reflection and endpoints, and repeats all 289,261,901 cells. |
| Theorems 3.1–3.3, Corollary 3.4, Proposition 4.1 | `scripts/regime-decomposition.py` | `certificates/regime-decomposition.txt` | Quadratic-form and discriminant identities; reflection identity on a grid; central identities; Riccati comparison algebra including the I1/I2 link identities; exact flow conjugacy `r_s = k/y_s` and the phi-comparison invariant on a grid; coverage margin; reflection-collapse formulas; exact small-grid coverage and gap census. |

## Finite-offset and fixed-argument certificates

| Manuscript result | Generator | Exact log | Obligations |
|---|---|---|---|
| Theorem 4.2 | `scripts/finite-gap-offsets.py`; `cpp/independent-certificate-check.cpp` | `certificates/finite-gap-offsets.txt`; `certificates/independent-finite-offset.txt` | The primary construction performs the stated fraction-free, gcd, factor, resultant, and census checks. The C++ checker reconstructs the recurrence forms, multiplies every exported factorization, repeats the sector-domination estimates, binds each resultant to its declared constraint pair, and verifies it by Sylvester determinants at one more point than its enforced degree bound. |
| Proposition 4.3 | `scripts/small-argument-cases.py` | `certificates/small-argument-cases.txt` | Exact binomial-ratio rational forms for `Q=0,1,2`; denominator orientation with square-factor nonvanishing on `u <= D-10`; paired domination for `S_2`; gap-strip containment with every quantified step ray-certified (including `h >= 2 sqrt(E)`); all twelve edge-flow inequalities on the ray `D >= 24`; direct-cell smallness asserted in the E2E gate. |
| Lemma 4.4, Theorem 4.5, and Corollary 4.6 | `scripts/fixed-argument-strips.py`; `cpp/independent-certificate-check.cpp` | `certificates/fixed-argument-strips.txt`; `certificates/independent-fixed-argument.txt` | The primary construction performs the stated strip and Sturm checks. The C++ checker reconstructs all four defining binomial-ratio sums on degree-complete exact grids, combines them symbolically, proves every denominator factor nonzero with fixed sign on an enlarged exact wedge, and repeats every ray/pairing Sturm certificate. |

The finite-offset source constructs the relevant polynomials recursively
rather than trusting hard-coded expansions. For each factor it recomputes
the exact mesh minimum, derivative bound, lower-degree coefficient bounds,
and resultant candidates. The committed log records the factor degrees,
multiplicities, domination onset, resultant degrees, and candidate counts.

The fixed-argument source constructs

`T/binom(M,s)^2 = R_0^2 + R_0 R_2 - R_1^2 - R_{-1} R_1`

from the finite product formula printed in the manuscript. It then computes
the coefficient polynomials and their signed Sturm chains; the complete
pairing indices and certified onsets are written to the log.

## Infinite residual regions

| Manuscript result | Generator | Exact log | Obligations |
|---|---|---|---|
| Theorem 5.1 | `scripts/even-minimum-gap.py` | `certificates/even-minimum-gap.txt` | Turán-step identity; positive-definite Turán form; the `(p,d)` system (the script's variable name is `h`); Riccati/tangent comparison identities; exact angular budget including the manuscript's 9/16 chain and its u >= 15 ray facts. This verifier is float-free: the orbit tan-bound comparison is exact, because tangent values along the orbit are rational multiples of `sqrt(Lambda)` and tan-addition preserves that form. |
| Lemma 6.1 and Theorem 6.2 | `scripts/odd-minimum-gap.py`; `cpp/independent-certificate-check.cpp` | `certificates/odd-minimum-gap.txt`; `certificates/independent-odd-minimum.txt` | The primary verifier performs the stated projective and endpoint checks. The C++ checker independently repeats both base-ray tests and all four substituted infinite-region sign certificates. |

For the odd-minimum endpoint step, the generator constructs `P_1`, `R_1`,
`X_min2`, and `X_max` from the cleared transition identity before checking
the four endpoint polynomials `O_1,...,O_4`. It records their term counts and
least coefficients and fails if any coefficient is negative.

## Exploratory artifacts (not part of the proof)

`scripts/finite-offset-limit.py` / `certificates/finite-offset-limit.txt`
and `scripts/uniform-limit-formula.py` /
`certificates/uniform-limit-formula.txt` study the joint central limit of
the reflection-collapse forms `M R_u^eps(M, tM)` (a Fejér-type positive
kernel; related to Question 1 of the manuscript's final section).  They
are **not** inputs to any theorem: no manuscript statement cites them,
and they are excluded from `PAYLOAD.sha256` (the proof-payload
identifier).  They are bound by `MANIFEST.sha256` only for snapshot
integrity.

## Replay

The short exact replays are:

```sh
python3 -u scripts/recurrence-and-small-scan.py
python3 -u scripts/regime-decomposition.py
python3 -u scripts/small-argument-cases.py
python3 -u scripts/even-minimum-gap.py
python3 -u scripts/odd-minimum-gap.py
```

The longer finite-family replays are:

```sh
python3 -u scripts/finite-gap-offsets.py 14
python3 -u scripts/fixed-argument-strips.py 12 14
```

The exhaustive scan is:

```sh
g++ -O2 -fopenmp -o /tmp/exhaustive-turan-scan \
  cpp/exhaustive-turan-scan.cpp -lgmpxx -lgmp
/tmp/exhaustive-turan-scan 1200
```

Use `make payload-check` and `make verify` to check the stored hashes. These
targets do not execute a proof program. Use `make replay-short` for the five
short exact replays and `make replay-all` for the complete proof replay.
Use `make toolchain-info` to print the active dependency versions and
`make audit-fast` for a short manifest/toolchain/integration audit.
Use `make replay-profile` when producing the machine-specific time and memory
report for a versioned release and persistent archival deposit.
Use `make audit-independent` for the second symbolic implementation, complete
Pascal scan, and mutation suite.
