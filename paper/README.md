# Monotonicity of Turán determinants for binary Krawtchouk polynomials

Source repository: <https://github.com/skypher/kraw>.  The manuscript on
`main` is Version 2.0.0 (October 2, 2026).

Build the manuscript deterministically in the reference toolchain from the
repository root with:

    make paper

The Makefile overrides any inherited `SOURCE_DATE_EPOCH` with the snapshot
value and enables the TeX source-date controls. The build requires the
standard AMS LaTeX packages and TikZ/PGF. Repeated builds are byte-identical
in the reference toolchain; byte identity across different TeX distributions
or font packages is not claimed.

For arXiv, upload `krawtchouk_turan_positivity.tex` and its `.bib` file
together at the root of the submission source. The figure is drawn by TikZ
within the manuscript. A current `.bbl` can also be included; arXiv uses it
in preference to running BibTeX, so regenerate it after bibliography edits.
DOI and arXiv links are included in the bibliography's `note` fields because
the `amsalpha` style does not render `doi` or `eprint` fields.

## Reproducing the verification logs

The programs require Python 3 and SymPy (reference: Python 3.12.3,
SymPy 1.12; wheel hashes in `requirements.txt`). Each exits nonzero on a
failed obligation and supports `-h`/`--help`. From the repository root:

    python3 -u scripts/recurrence-and-small-scan.py
    python3 -u scripts/regime-decomposition.py
    python3 -u scripts/even-minimum-gap.py
    python3 -u scripts/odd-minimum-gap.py

`make replay` runs all four and compares each output byte-for-byte with the
committed log in `certificates/`; elapsed times are not printed, so
successful reruns are identical. `make toolchain-info` prints the active
versions, and `make payload-check` / `make verify` check the stored hashes
(integrity only; they do not execute the programs).

The Lean formalization in `lean/` builds with `make lean` after
`lake exe cache get` has fetched the Mathlib build for the pinned version.
