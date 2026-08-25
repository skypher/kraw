# Monotonicity of Turán determinants for binary Krawtchouk polynomials

This repository contains the standalone manuscript, exact-arithmetic
verification outputs, and programs for the theorem that the Turán
determinant of

\[
  [w^s](1+w)^M(1-w)^Q
\]

is non-increasing on the top half of the coefficient index, for all
nonnegative integers \(M,Q\).

The canonical repository is <https://github.com/skypher/kraw>.  Reviewed
artifact snapshots are identified by `certificates/MANIFEST.sha256`, which
hashes the manuscript, verifier sources, and deterministic outputs.
The stable proof payload is listed separately in
`certificates/PAYLOAD.sha256`; `certificates/CERTIFICATE_MAP.md` maps each
machine-assisted theorem to its exact generator and replay log, and
`certificates/REVIEW_CHECKLIST.md` gives a function-by-function referee
inspection path. `certificates/REPLAY_PROFILE.md` records the measured
complete replay shipped with release `v1.0.2`.

## Layout

- `paper/` — LaTeX manuscript, bibliography, and PDF.
- `scripts/` — SymPy exact-arithmetic verification programs.
- `cpp/` — GMP exhaustive scanner.
- `certificates/` — committed verification outputs and their hash manifest.

## Reproduction

Build the PDF deterministically in the documented reference toolchain from
the repository root with:

```sh
make paper
```

The Makefile overrides any inherited `SOURCE_DATE_EPOCH` with the reviewed
snapshot value and enables the TeX source-date controls. Repeated builds are
byte-identical in the documented reference toolchain; byte identity across
different TeX distributions or font packages is not claimed.

Check the stored proof-payload and artifact hashes with:

```sh
make payload-check
make verify
```

These targets check snapshot integrity; they do not execute the proof
programs. Run the short exact replays with `make replay-short`, or all proof
programs, including the multi-hour symbolic jobs and exhaustive GMP scan,
with `make replay-all`. Use `make replay-profile` to run that complete replay
under `/usr/bin/time -v` and capture a machine-specific resource report for
an archival release. The `v1.0.2` reference run is summarized in
`certificates/REPLAY_PROFILE.md`; its path-sanitized transcript is a release
asset.

Before a replay, print the active dependency versions with:

```sh
make toolchain-info
```

For a practical first audit, `make audit-fast` checks both manifests, prints
the toolchain, runs all short exact verifiers, compiles the GMP scanner, and
scans through `D <= 120`. It does not replace `make replay-all`.

The paper needs standard AMS LaTeX packages and TikZ/PGF.  The exact
verification commands and requirements are documented in `paper/README.md`;
the Python dependency is pinned in `requirements.txt`.

The manuscript is the current mathematical statement.
