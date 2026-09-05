# Monotonicity of Turán determinants for binary Krawtchouk polynomials

Source repository: <https://github.com/skypher/kraw>.  The
`certificates/MANIFEST.sha256` file identifies a reviewed artifact snapshot
by hashing the manuscript, verifier sources, and deterministic outputs.
The manuscript on `main` is Version 1.0.8 (September 5, 2026).
Its verification programs and deterministic logs are unchanged from the
[v1.0.6 release](https://github.com/skypher/kraw/releases/tag/v1.0.6).
`certificates/PAYLOAD.sha256` is the noncircular proof-payload identifier.
`certificates/CERTIFICATE_MAP.md` maps the computer-assisted results to their
generators and exact logs, and `certificates/REVIEW_CHECKLIST.md` gives a
function-by-function inspection path and the acceptance predicate of each
verifier. `certificates/REPLAY_PROFILE.md` records the complete replay retained
for v1.0.4, while `certificates/INDEPENDENT_REPLAY_PROFILE.md` records the
local v1.0.5 assurance runs and their limits.
`certificates/INDEPENDENT_CHECKS.md` specifies the separate C++ checker,
Pascal scan, and mutation tests.

Build the manuscript deterministically in the reference toolchain from the
repository root with:

    make paper

The Makefile overrides any inherited `SOURCE_DATE_EPOCH` with the reviewed
snapshot value and enables the TeX source-date controls. The build requires
the standard AMS LaTeX packages and TikZ/PGF. Repeated builds are
byte-identical in the reference toolchain; byte identity across different
TeX distributions or font packages is not claimed.

For arXiv, upload `krawtchouk_turan_positivity.tex` and its `.bib` file
together at the root of the submission source. The figure is drawn by TikZ
within the manuscript. A current `.bbl` can also be included; arXiv uses it
in preference to running BibTeX, so regenerate it after bibliography edits.
DOI and arXiv links are included in the bibliography's `note` fields because
the `amsalpha` style does not render `doi` or `eprint` fields. Keep each DOI
link consistent with its corresponding `doi` field. See the
[arXiv TeX instructions](https://info.arxiv.org/help/submit_tex.html).

## Reproducing the verification artifacts

Run these commands from the repository root. Python checks require Python 3
and SymPy; the exhaustive scan requires a C++17 compiler and GMP/GMPXX.
The independent checker and second scan require the Boost multiprecision
headers.
The reference environment used Python 3.12.3, SymPy 1.12, g++ 13.3,
and GMP 6.3.0.  Each verifier exits nonzero on a failed obligation.
The Python dependencies and wheel hashes are pinned in `requirements.txt`.
The machine-readable reference environment is in `environment/`; its Ubuntu
base image, package snapshot, and Python wheels are fixed independently.

Print the corresponding versions in the active environment with:

    make toolchain-info

Run the manifests, toolchain report, five short exact replays, mutation tests,
and compiled GMP and Pascal scans through `D <= 120` with:

    make audit-fast

This is a fast environment and integration audit, not a substitute for the
complete replay below.

    python3 -u scripts/recurrence-and-small-scan.py
    python3 -u scripts/regime-decomposition.py
    KRAW_EXPORT_WITNESS=certificates/independent-finite-offset.txt python3 -u scripts/finite-gap-offsets.py 14
    python3 -u scripts/small-argument-cases.py
    KRAW_EXPORT_WITNESS=certificates/independent-fixed-argument.txt python3 -u scripts/fixed-argument-strips.py 12 14
    python3 -u scripts/even-minimum-gap.py
    KRAW_EXPORT_WITNESS=certificates/independent-odd-minimum.txt python3 -u scripts/odd-minimum-gap.py
    g++ -O2 -fopenmp -o /tmp/exhaustive-turan-scan cpp/exhaustive-turan-scan.cpp -lgmpxx -lgmp
    /tmp/exhaustive-turan-scan 1200
    make audit-independent

The finite-gap-offset and fixed-argument-strip runs are the longer symbolic
stages. Deterministic committed replay logs are in `certificates/`; elapsed
times are intentionally omitted so that successful reruns are byte-for-byte
comparable. Their hashes, together with hashes of the verifier sources, are
recorded in `certificates/MANIFEST.sha256`.

For a new machine, record actual resource use outside the deterministic logs,
for example with `/usr/bin/time -v make replay-all`.  Do not copy timing or
memory figures from another host into a reproducibility report.

The same commands are available as `make replay-short` (the five short exact
replays) and `make replay-all` (all proof programs, witness regeneration, and
independent checks).  The witness-export stage alone is available as
`make export-independent-witnesses`. After replaying them,
check the stored artifact hashes from the repository root with:

    make payload-check
    make verify

These two targets check snapshot integrity only; they do not execute the
proof programs.

For the archival resource report, run:

    make toolchain-info
    make replay-profile

Record the toolchain output, elapsed time, peak resident memory, and exit
status with the versioned release. The v1.0.4 reference run is summarized in
`certificates/REPLAY_PROFILE.md`; local v1.0.5 assurance timings are in
`certificates/INDEPENDENT_REPLAY_PROFILE.md`. Path-sanitized transcripts belong
with the corresponding release rather than in the deterministic logs.

The repository also retains two supplementary asymptotic checks, which are
not used in the proof:

    python3 -u scripts/finite-offset-limit.py
    python3 -u scripts/uniform-limit-formula.py
