# Monotonicity of Turán determinants for binary Krawtchouk polynomials

This repository contains the manuscript, its exact-arithmetic verification
programs and deterministic logs, and a complete Lean 4 formalization of the
theorem that the Turán determinant of

\[
  [w^s](1+w)^M(1-w)^Q
\]

is non-increasing on the top half of the coefficient index, for all
nonnegative integers \(M,Q\).

The canonical repository is <https://github.com/skypher/kraw>.  The manuscript
on `main` is Version 2.0.1 (October 3, 2026).  Version 2 restructures the
proof so that no finite enumeration is needed: even smaller exponents are
handled by a tangent comparison for every gap offset, and odd ones by an
interval propagation whose four polynomial inequalities are certified by
coefficient positivity.  The finite-offset, fixed-argument, and exhaustive-scan
programs of Version 1 are therefore retired; they remain in the git history
(tag `v1.0.6`).  Version 2.0.1 applies the corrections from a fidelity audit
of the Lean formalization against the paper (recorded in `lean/ROADMAP.md`).
It drops an unused hypothesis from one Lean statement, rewords the Figure 1
caption, and fixes documentation.

`certificates/MANIFEST.sha256` hashes every artifact file, and
`certificates/PAYLOAD.sha256` hashes the verification payload without the
manuscript, so its digest can be printed in the paper.
`certificates/CERTIFICATE_MAP.md` maps each computer-checked statement to its
program and log, and `certificates/REVIEW_CHECKLIST.md` gives an inspection
path through the programs.

## Layout

- `paper/` — LaTeX manuscript, bibliography, and PDF.
- `scripts/` — SymPy exact-arithmetic verification programs.
- `certificates/` — committed verification logs and hash manifests.
- `lean/` — Lean 4 / Mathlib formalization of every numbered statement and
  displayed claim of the paper; `lean/Kraw/Paper.lean` indexes them by number and
  `lean/ROADMAP.md` maps each Lean file to the paper.

## Licensing

The executable code (`scripts/`, `lean/`, the Makefile, the locked
environment, and CI workflow) is licensed under the BSD 3-Clause License.
The manuscript and explanatory documentation are licensed under the Creative
Commons Attribution 4.0 International License. See `LICENSE` for the precise
component boundaries and terms.

## Reproduction

From the repository root:

```sh
make paper          # deterministic PDF build in the reference toolchain
make payload-check  # hashes of the verification payload
make verify         # hashes of every artifact file
make replay         # run all four programs and diff against the committed logs
make audit-fast     # verify + toolchain-info + replay
make lean           # build the Lean formalization and check its axioms
                    # (needs elan; run `cd lean && lake exe cache get` first)
```

`make replay` takes about a minute.  GitHub Actions
(`.github/workflows/audit-fast.yml`) runs `make audit-fast` and `make lean` on
every push and pull request; the Lean job uses a pinned, checksum-verified elan
and takes about six minutes.  The Python dependencies and wheel hashes
are pinned in `requirements.txt`; `environment/Dockerfile` pins a reference
Ubuntu image and package snapshot.  The exact commands are documented in
`paper/README.md`.
