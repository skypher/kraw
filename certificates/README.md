# Verification artifacts

Each `.txt` file in this directory is the deterministic standard output of
the source program with the same stem in `scripts/`, except that
`exhaustive-scan-D1200.txt` is produced by `cpp/exhaustive-turan-scan.cpp`.
The exact replay commands and reference dependency versions are listed in
`paper/README.md`.

The logs are execution records, not stand-alone proofs.  The corresponding
source programs construct the displayed polynomial identities and check all
sign, Sturm, resultant, coverage, and recurrence obligations in exact
arithmetic.  The proof programs are float-free: every check, including the
end-to-end orbit walks, uses integer or rational arithmetic.

The exhaustive GMP scanner checks divisibility before each exact recurrence
division, compares every coefficient with the binomial definition for
`D <= 12`, and audits deterministic coefficients in six larger rows up to
`D = 1200`.

The `independent-*.txt` files are machine-readable exact witnesses or replay
records for a second implementation.  `cpp/independent-certificate-check.cpp`
checks the exported polynomial identities, factors, Sturm obligations, and
resultants without SymPy or GMP.  `cpp/independent-pascal-scan.cpp` repeats the
complete finite scan using Boost integers and a two-parent Pascal construction
instead of the Krawtchouk row recurrence.  The precise separation of the two
implementations is documented in `INDEPENDENT_CHECKS.md`.

The detailed finite-offset log reports each parity's factor-degree pattern,
large-parameter threshold, resultant degree, and number of integer
candidates.  The fixed-argument log reports every paired coefficient and its
Sturm onset.  The odd-minimum log reports the exact successor-window identity,
the endpoint-polynomial term counts and least coefficients, and any Sturm
fallbacks.

`CERTIFICATE_MAP.md` gives the theorem-by-theorem trust boundary and replay
map. `PAYLOAD.sha256` hashes the proof generators, dependency locks, license,
map, referee checklist, and exact logs without including the manuscript; its
digest can therefore serve as a noncircular proof-payload identifier printed
in the paper.
`REVIEW_CHECKLIST.md` gives a function-by-function inspection path and states
the acceptance predicate of every proof generator.
`INDEPENDENT_REPLAY_SIGNOFF.md` is an intentionally unsigned form for the
required clean replay by another person; its blank status must not be read as
a completed review. `INDEPENDENT_REPLAY_PROFILE.md` records local v1.0.5 runs
separately and explicitly does not count as that human sign-off.

Run

```sh
make payload-check
make verify
```

from the repository root to check the hashes of the proof payload and then
the complete source/output snapshot. These are integrity checks, not proof
replays. Use `make replay-short` for the five short exact programs and
`make replay-all` for the complete replay, including the longer symbolic
certificates, both exhaustive scans, and the independent witness checks.

Use `make toolchain-info` to record dependency versions and `make audit-fast`
for a short manifest/toolchain/integration audit before starting the complete
replay. `make replay-profile` runs the complete replay under
`/usr/bin/time -v`; its machine-specific output belongs in the versioned
release record, not in the deterministic proof logs.

Run `make audit-independent` to compile and execute the independent symbolic
checker, the full Boost/Pascal scan, and all mutation tests.  The witness files
can be regenerated with `make export-independent-witnesses`.

The primary proof-generating programs rely on the exact-arithmetic
implementations in their declared trusted base.  The independent layer checks
their decisive outputs through separately implemented exact arithmetic; it
does not make the compiler, Boost integer primitives, or the independent
checker source disappear from the trust boundary.
