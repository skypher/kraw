# Verification artifacts

Each `.txt` file in this directory is the deterministic standard output of
the program with the same stem in `scripts/`.  `make replay` reruns every
program and compares its output byte-for-byte with these logs.

The logs are execution records, not stand-alone proofs.  The programs
construct the displayed polynomial identities and check every sign
obligation in exact rational arithmetic; no floating-point value, asymptotic
estimate, or finite enumeration is used to prove the Main Theorem.  The only
inequalities established by computer are the four obligations `O_1`–`O_4`
of Lemma 5.2, each certified by expanding a polynomial after an explicit
substitution and checking that every coefficient is nonnegative.  The programs also walk the recurrence exactly over finite
ranges as consistency checks of the induction invariants; these walks are
not proof steps.

`CERTIFICATE_MAP.md` maps each statement of the manuscript to its program and
log.  `REVIEW_CHECKLIST.md` gives an inspection path and the acceptance
predicate of every program.  `PAYLOAD.sha256` hashes the programs, logs,
dependency lock, license, map, checklist, and the Lean sources without the
manuscript; its digest is printed in the paper.  `MANIFEST.sha256` hashes
every artifact file, including the manuscript and PDF.

    make payload-check
    make verify
    make replay
