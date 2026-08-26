# Independent software checks

The primary proof programs remain the certificate producers: they derive the
polynomial identities from the recurrences and emit the exact witness files
listed below.  A second implementation then checks the decisive exported
objects without using SymPy or GMP.

## Independent implementations

- `cpp/independent-pascal-scan.cpp` constructs every coefficient row through
  the two Pascal parents
  `(1+w)p(M-1,Q)` and `(1-w)p(M,Q-1)`.  Interior rows must agree coefficient by
  coefficient.  It uses Boost `cpp_int`, checks reflection and endpoints, and
  scans every one of the 289,261,901 top-half cells through `D=1200`.  This is
  independent of the GMP scanner's within-row three-term recurrence.
- `cpp/independent-certificate-check.cpp` and
  `cpp/exact-polynomial.hpp` implement rational arithmetic, sparse polynomial
  arithmetic, Euclidean division, Sturm chains, Sylvester determinants, and
  modular no-root tests directly over Boost integers.
- `certificates/independent-fixed-argument.txt` exports the reduced numerator,
  denominator factors, coefficient polynomials, and all four reduced
  binomial-ratio fractions.  The checker reconstructs each defining finite
  sum on a grid whose size follows from an explicit total-degree bound,
  combines the four fractions symbolically, proves every denominator factor
  nonzero with fixed sign on the exact enlarged wedge, and independently
  repeats every ray and pairing Sturm test.
- `certificates/independent-finite-offset.txt` exports each quadratic-form
  identity, common-factor division, reduced factorization, sector-positivity
  data, resultant, and resultant factorization.  The checker first reconstructs
  λ, μ, A, B, and C from the fraction-free recurrence, then multiplies every
  factorization, repeats the mesh/derivative/lower-layer domination argument,
  binds every resultant to the exact constraint polynomials it is meant to
  eliminate, and verifies it as a Sylvester determinant at one more integer
  point than its enforced degree bound.  A nonlinear resultant factor is
  accepted only with a checked prime at which it has no root.
- `certificates/independent-odd-minimum.txt` exports both base-ray obligations
  and the four infinite-region endpoint polynomials.  The checker independently
  performs the substitutions and Sturm/coefficients tests on both pieces of
  the region.

The witness generators checkpoint after every completed fixed argument or
finite offset.  A final file receives its `END` marker and atomically replaces
the target only after the original producer has accepted every obligation.

## Mutation tests

`scripts/mutation-test-independent.sh` injects five faults into the independent
Pascal scan: each parent construction, an endpoint, the Turán comparison, and
the asserted cell count.  `scripts/mutation-test-certificates.sh` changes an
odd-region sign, a fixed-strip content polynomial, a reconstructed ratio, a
finite recurrence polynomial, a finite-offset factor, a resultant, and a
resultant-to-constraint link.  Every mutated execution must return nonzero.

Run the software-independent layer with:

```sh
make independent-check
make independent-scan
make mutation-test
```

or run all three through `make audit-independent`.

## Remaining trust boundary

This layer removes SymPy's factorization, gcd, resultant, and Sturm routines,
and the GMP recurrence scanner, from the shared decisive implementation path.
It still trusts the C++ compiler, Boost's integer primitives, this repository's
small exact-arithmetic implementation, and the mathematical degree bounds and
certificate formats documented above.  A clean replay by another person is a
separate acceptance step; its unsigned record is
`INDEPENDENT_REPLAY_SIGNOFF.md`.
