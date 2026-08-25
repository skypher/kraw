# Referee checklist for the computer-assisted proof

This checklist is an inspection guide for the exact source snapshot. It is
more detailed than the theorem-to-file map in `CERTIFICATE_MAP.md`: it names
the constructors, the acceptance predicates, and the finite data that a
reviewer should inspect or replay. The deterministic `.txt` files remain
execution records, not stand-alone proof objects.

All proof decisions use integer or rational arithmetic. The trusted
high-level operations are SymPy's polynomial factorization, polynomial gcd,
resultant, and Sturm root counting, plus GMP integer arithmetic. The proof
programs are float-free: every check that feeds an acceptance predicate,
including the end-to-end orbit walks, is exact.

## Global recurrence and finite scan

### `scripts/recurrence-and-small-scan.py`

- `coefficients(M,Q)` constructs the defining binomial convolution.
- `main()` checks the coefficient recurrence for every `M,Q <= 30`.
- `main()` evaluates every top-half Turán step for `M,Q <= 90`.
- Acceptance is the conjunction of the exact recurrence identities and the
  absence of a negative integer Turán step.

### `cpp/exhaustive-turan-scan.cpp`

- The `DMAX` argument is validated (malformed or nonpositive input
  aborts with a distinct exit code rather than scanning an empty
  range); the default is the manuscript's 1200.
- Each row starts from `p[0]=1`, `p[1]=M-Q`.
- Before each `mpz_divexact_ui`, `mpz_divisible_ui_p` checks divisibility;
  a failed row is abandoned without emitting secondary diagnostics, and
  the nonzero structural code still forces a failing exit.
- Every coefficient is compared with the binomial convolution for `D <= 12`.
- Five deterministic coefficients are compared in each of six larger rows.
- The endpoint `p[D]=(-1)^Q`, the total cell count (asserted in-program
  against the closed-form sum, with a distinct failing exit code on
  mismatch), and absence of negative Turán steps are required for
  acceptance.  The structural counters are printed to stdout, so the
  committed log records them.

## Regime decomposition and small offsets

### `scripts/regime-decomposition.py`

`main()` reconstructs rather than hard-codes:

- the quadratic form for `T_s` and its discriminant;
- the reflection identity `p_{D-j} = (-1)^Q p_j` (grid) and the
  central identities in both reflection parities;
- every algebraic identity in the Riccati-flow comparison, including
  the link identities tying `I_1` and `I_2` to the quadratic form;
- the coverage margin at the flow boundary;
- all six reflection-collapse formulas for `u=1,2,3`;
- the first residual gap witnesses (the `D = 442` census consumed by
  the finite-gap-offsets sector bound, and independently repeated
  there).

The flow grid check verifies the theorem's exact conjugacy
`r_s = k/y_s` and the comparison invariant `y_s >= phi(s)` (via
squares) in exact rational arithmetic, using the manuscript's own
auxiliary flow.  The exact grid checks are diagnostics supporting the
symbolic identities; they are not used to extend a finite statement to
an infinite region.

### `scripts/small-argument-cases.py`

- `strip_form` builds `T/binom(M,s)^2` from the binomial-ratio formula
  and pins the closed forms `N_0`, `N_1`, `N_2 = D(D-1)S_2` by exact
  division and coefficient identities.
- The denominator orientation is certified on `u <= D-10` (the domain
  the proof uses) with square factors machine-checked nonvanishing.
- Every quantified inequality in the strip-containment chain --
  including `h >= 2 sqrt(E)` and all twelve edge-flow inequalities on
  `D >= 24` -- is certified on its full ray by coefficient
  nonnegativity, not by spot evaluation.
- The E2E gate additionally asserts that every direct-only cell has
  `D < 24` (scan-covered).

## Finite gap offsets

### `scripts/finite-gap-offsets.py`

For each `u=4,...,14` and `eps` in `{+1,-1}`:

1. `scaled_chain` constructs the fraction-free recurrence from two formal
   seeds with `c[0]=c[1]=1` (or the shifted initialization for the alternate
   pinning).
2. `build_G` constructs the reflection constraint `(lambda,mu)`, the
   quadratic form `Ttilde`, and
   `G=A*mu^2-B*lambda*mu+C*lambda^2`. It checks both constrained-form
   identities by exact expansion.
3. `reduce_version` removes `gcd(lambda,mu)` and checks
   `G=g^2*G_reduced` exactly.
4. `cert_positive` factors `G_reduced`. Even-multiplicity factors are
   nonnegative. For every odd factor, `cert_factor` computes:
   - the leading homogeneous polynomial on
     `0 <= Q/M <= 1/(u+1)^2`;
   - its exact 513-point mesh minimum;
   - an exact derivative bound between mesh points;
   - exact absolute bounds for every lower homogeneous layer;
   - the first integer domination threshold.
5. `no_common_sector_zeros` forms the resultant in `Q`, factors the
   resultant over the integers, enumerates every integer `M` candidate, and
   checks each specialized gcd in `Z[Q]` (integer arithmetic throughout;
   an identically vanishing specialized gcd is a failure, not a skip).
6. If the first common factor can vanish, the same construction is repeated
   with the alternate reflection pinning -- including the reduced-pair
   nondegeneracy check for the second pinning, which is required
   unconditionally. A second resultant check excludes a simultaneous zero
   of the two common factors.
7. The `[S]` block repeats, in-script, the heredity-reduced exact census
   that no gap cell with `u >= 4`, `Q >= 3` has `D < 442`; this is the
   input to the sector bound `M >= 425`.
8. `numeric_spot` evaluates each constrained identity at the first gap
   cells of each Q-parity; the tested counts are printed and at least one
   cell per parity is required (a vacuous spot run fails).
9. `first_open_gap` performs the exact threshold census from `D = 4`
   using strict integer inequalities and parity-compatible candidates,
   and the canonical `UMAX = 14` run asserts the manuscript's census
   values `(4587, 3, 15)`.

Acceptance requires every symbolic identity, factor sign, domination
threshold (with the manuscript bound `M0 <= 153` asserted), reduced-pair
nondegeneracy test for both pinnings, alternate-pinning test, and
threshold census to pass. Internal construction identities are hard
gates raising a nonzero exit even under `python3 -O`. The committed log
reports every factor multiplicity, core degree and domination onset,
resultant degree, and integer-candidate count.

## Fixed-argument strips

### `scripts/fixed-argument-strips.py`

For each `Q=3,...,12`:

1. `strip_form` constructs `T/binom(M,s)^2` from the finite binomial-ratio
   formula printed in the paper, substitutes `M=D-Q` and `s=(D+u)/2`, and
   fixes the denominator orientation.  (Convention note: the script
   orients the denominator negative and flips the numerator sign; the
   manuscript states the equivalent positive orientation.  The certified
   sign of `S_Q/denominator` is identical.)
2. `den_negative` classifies every denominator factor on the strip
   `0 <= u <= D-2Q-6`: positive factors, an odd count of negative
   factors, and even-multiplicity factors whose zero locus lies
   strictly above the strip -- so the squares are machine-certified
   nonvanishing there, not assumed.
   The per-`Q` numeric identity spot check counts its admissible cells;
   a vacuous spot run is a failure.
3. `certify_Q` removes the common positive coefficient content and derives
   every coefficient polynomial `c_j(D)`.
4. For every negative coefficient, `certify_Q` verifies with exact Sturm
   counts that:
   - `c_j(D)<0`;
   - its unused partner `c_{j-2}(D)>0`;
   - `c_{j-2}(D)+c_j(D) B_Q(D)>0`
     at the manuscript's common onset `D_0(Q) = 2Q+6` exactly -- a
     family needing a later onset is a FAIL, not a silent fallback.
   The discovered partner set is asserted against the manuscript's
   pattern (`4r, 4r+1` for even `Q`; `4r+2, 4r+3` for odd `Q`).
5. Every unpaired coefficient is independently certified positive on the
   same ray.
6. The top-edge flow inequality is scanned exactly for its first permanent
   integer onset and checked against the onset printed in the manuscript;
   the first-open-cell census runs from `D = 4` (no external premise)
   and the canonical `Q0 = 12`, `UMAX = 14` run asserts the
   manuscript's census values `(14827, 13, 15)`.

Acceptance requires all coefficient signs, all pair inequalities and the
partner pattern, the denominator orientation with square nonvanishing,
the exact edge-flow onset, and the asserted threshold census.
The complete partner list and each onset are printed in the log.

## Infinite residual regions

### `scripts/even-minimum-gap.py`

`main()` checks by exact symbolic simplification the Turán-step identity,
positive-definite Turán form, the `(p,d)` recurrence (the script's
variable name is `h`), Riccati map, tangent addition identity, both
parity anchors, and every inequality in the angular budget -- including
the manuscript's constant 9/16 and the sharper `u = 15` instance 17/32,
each with its `u >= 15` ray fact certified by coefficient nonnegativity.
Jordan's inequality is classical and enters only as the cited reduction
step; the `pi/2` factors cancel, so no numerical value of `pi` is used.
The end-to-end orbit walk is exact, including the tan-bound comparison:
along the orbit each tangent value is a rational multiple of
`sqrt(Lambda)` (base cases `tan th* = sqrt(Lambda)/x` and
`tan(th*/2) = sqrt(Lambda)/(D+2+x)`, step
`t -> (t x + 1)/(x - t Lambda)`), so the invariant
`zeta <= t*Lambda < x` is pure `Fraction` arithmetic and the positivity
of every step denominator certifies that the orbit angle stays below
`pi/2`. This verifier is float-free.

### `scripts/odd-minimum-gap.py`

- `main()` constructs the projective Möbius map, positivity window, roots,
  both parity anchors, and the cleared successor-window identity.
- For the odd-$D$ base inequality, `main()` checks the exact concavity
  coefficient identity `[x^2]S_{\rm odd}=-4(D+1)(D+5)` before checking the
  two endpoint values; the endpoint denominators must be certified
  positive (an uncertified denominator is a FAIL, never silently
  patched).
- It derives `P_1`, `R_1`, `X_min2`, and `X_max` from that identity --
  with `K`'s denominator cleared by the positive square `(D+u+4)^2`,
  exactly as displayed in the manuscript -- before testing signs, and
  certifies `K > 0` together with the monotonicity of `K x(u+1)` in
  `X` from the coefficient positivity of the shared numerator `N`.
- `poly_nonneg_region` checks the four endpoint obligations after the exact
  substitutions used in the manuscript. It requires coefficient
  nonnegativity, or an exact Sturm fallback when coefficient positivity does
  not apply.
- The transition through the infinite projective state and the
  manuscript's region-bound chain (through `24(D+3) >= 289`) are checked
  symbolically or by ray certificates.
- This verifier is float-free; its end-to-end recurrence walk is exact.

Acceptance is the conjunction of these identities and sign obligations.
The log records endpoint term counts, least coefficients, and every Sturm
fallback.

## Required replay sequence

From the repository root:

```sh
make payload-check
make verify
make toolchain-info
make replay-all
```

The first two commands verify identity of the reviewed snapshot. Only
`replay-all` executes every proof program. An accepted version should cite a
persistent, DOI-bearing archive of this exact payload and include an
independently recorded wall-time and peak-memory report for the complete
replay.
