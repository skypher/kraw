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
The manuscript on `main` is Version 1.0.6 (September 4, 2026).
The stable proof payload is listed separately in
`certificates/PAYLOAD.sha256`; `certificates/CERTIFICATE_MAP.md` maps each
machine-assisted theorem to its exact generator and replay log, and
`certificates/REVIEW_CHECKLIST.md` gives a function-by-function referee
inspection path. `certificates/REPLAY_PROFILE.md` records the measured
complete replay retained for v1.0.4;
`certificates/INDEPENDENT_REPLAY_PROFILE.md` records the local v1.0.5
assurance runs and their limits.

## Layout

- `paper/` — LaTeX manuscript, bibliography, and PDF.
- `scripts/` — SymPy exact-arithmetic verification programs.
- `cpp/` — GMP scanner plus the independent Boost/Pascal scan and symbolic
  checker.
- `certificates/` — committed verification outputs and their hash manifest.

## Licensing

The executable proof code (`scripts/`, `cpp/`, the Makefile, the locked
environment, and CI workflow) is licensed under the BSD 3-Clause License.
The manuscript and explanatory documentation are licensed under the Creative
Commons Attribution 4.0 International License. See `LICENSE` for the precise
component boundaries and terms.

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
programs and independent checks, including the longer symbolic certificates
and both exhaustive scans, with `make replay-all`. Use `make replay-profile` to run that complete replay
under `/usr/bin/time -v` and capture a machine-specific resource report for
an archival release. The v1.0.4 reference run is summarized in
`certificates/REPLAY_PROFILE.md`; the Version 1.0.5 independent component
runs are in `certificates/INDEPENDENT_REPLAY_PROFILE.md`.

Before a replay, print the active dependency versions with:

```sh
make toolchain-info
```

For a practical first audit, `make audit-fast` checks both manifests, prints
the toolchain, runs all short exact verifiers and the independent checker,
executes all mutation tests, and runs both compiled scanners through
`D <= 120`. It does not replace `make replay-all`.

The separate software-assurance layer is described in
`certificates/INDEPENDENT_CHECKS.md`.  Run `make audit-independent` to replay
the exported witnesses with the standalone C++ polynomial/Sturm/resultant
checker, repeat all 289,261,901 finite cells through an independent
Boost/Pascal construction, and verify that all injected mutations are
rejected.  Independent human replay remains a separately signed step; the
blank form is `certificates/INDEPENDENT_REPLAY_SIGNOFF.md`.

The paper needs standard AMS LaTeX packages and TikZ/PGF.  The exact
verification commands and requirements are documented in `paper/README.md`;
the Python dependencies and wheel hashes are pinned in `requirements.txt`.
`environment/Dockerfile` pins the reference Ubuntu image by digest and uses a
dated Ubuntu package snapshot. Build it from the repository root with
`docker build -f environment/Dockerfile -t kraw-audit .`; its default command
runs `make audit-fast`.

The manuscript is the current mathematical statement.
