# Local independent-assurance replay profile — Version 1.0.5

Status: **local component replay passed; independent human sign-off remains
unsigned**

Date: 2026-08-26

This report records runs performed while constructing the independent
software-assurance layer.  It is not the clean third-party replay requested in
`INDEPENDENT_REPLAY_SIGNOFF.md` and does not replace that acceptance step.

## Reference toolchain

- Python 3.12.3
- SymPy 1.12
- g++ 13.3.0
- Boost headers 1.83.0-2.1ubuntu3.2
- GMP 6.3.0
- pdfTeX 1.40.25

The independent C++ executable was checked with `ldd`; it links the standard
C++ runtime and `libgomp`, but not GMP, Python, or SymPy.

## Final-source independent runs

| Run | Result | Wall time | Peak RSS |
|---|---:|---:|---:|
| Standalone exact witness checker: odd minimum, fixed Q=3,…,12, 44 finite cases, 66 resultants | 537 checks, 0 failures | 363.02 s | 24,576 KiB |
| Boost/two-parent Pascal scan through D=1200 | 289,261,901 cells, 0 negatives | 200.59 s | 401,068 KiB |
| Five scan mutations plus seven symbolic mutations, including the required clean symbolic baseline | 12/12 rejected | 436.44 s | 564,780 KiB |

During final-source validation, the repository's exact CI entry point,
`make audit-fast`, passed with exit status 0 in 14:44.46 and used 563,480 KiB
peak RSS.  That integrated run rechecked both then-current manifests, printed
the toolchain, ran all five short primary verifiers, repeated the 537-check
independent replay, rejected all twelve mutations, and ran both scanners
through D=120.  After release-label edits, `make verify` rechecked the final
v1.0.5 payload and full manifest.

The Pascal scan also recorded 576,719,000 alternate-parent coefficient
comparisons, 578,162,601 reflection checks, and 1,443,602 endpoint checks.
Its deterministic stdout was byte-identical to
`independent-scan-D1200.txt`.  The standalone checker's stdout and the mutation
suite's stdout were likewise copied byte-for-byte into their committed replay
records.

Both independent sources compile as C++17 under g++ with
`-Wall -Wextra -Werror -pedantic`.  As a compiler-diversity smoke test,
Clang 18.1.3 compiled
sequential versions with warnings treated as errors; the exact-arithmetic and
odd-minimum tests passed, as did all 300,791 Pascal cells through D=120.

## Primary-producer cross-checks

The odd-minimum, fixed-argument, and finite-offset witness producers all
exited successfully.  Their ordinary deterministic stdout was byte-identical
to the corresponding primary committed log.  The completed finite witness
contains exactly 44 finite-case records and 66 resultant records and ends in
the atomic `END` marker.  After that run, stderr-only subphase markers were
added to the finite producer so future long replays expose recurrence,
reduction, factor, resultant, and root-census advancement; those markers do
not change the deterministic stdout or witness format.

The five short primary verifiers were also replayed successfully in 105.72 s
with 119,808 KiB peak RSS.  The complete primary baseline retained for v1.0.4
remains documented in `REPLAY_PROFILE.md`.

The v1.0.5 manuscript rebuilt successfully to 31 pages.  `qpdf --check`
reported no syntax or stream-encoding errors; `pdfinfo` parsed all pages;
`pdffonts` reported every font embedded; and the final LaTeX log contained no
overfull box, undefined reference, or undefined citation.

## Outstanding independent acceptance step

No second person has yet performed and signed a fresh-checkout replay of
v1.0.5.  The blank protocol in `INDEPENDENT_REPLAY_SIGNOFF.md` therefore
remains unsigned.  A pinned Docker recipe is included, but this account did
not have permission to access the local Docker daemon; a build of the final
image is part of the clean external replay.
