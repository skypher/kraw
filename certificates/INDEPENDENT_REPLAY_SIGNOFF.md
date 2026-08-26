# Independent replay sign-off

Status: **unsigned — independent human replay still required**

This record must be completed by a person who did not author the proof or its
verification programs.  An automated agent run is not a substitute for this
sign-off.

## Snapshot identification

- Reviewer:
- Affiliation or contact:
- Replay date (UTC):
- Git commit:
- Release/tag:
- `PAYLOAD.sha256` file digest:
- Container image ID and digest, or exact native toolchain report:

## Required clean commands

```sh
make payload-check
make verify
make toolchain-info
make replay-all
make audit-independent
make pdf-preflight
```

Record for each command its exit status, wall time, and peak resident memory.
Attach the complete unedited transcript.  Confirm separately that:

- the checkout was fresh and contained no uncommitted changes before replay;
- no committed log was used as a substitute for executing its generator;
- all 289,261,901 cells were checked by both finite scanners;
- all twelve injected mutations were rejected;
- the regenerated witness files and deterministic logs match the committed
  files byte for byte;
- any exception, warning, or environmental difference is described below.

## Result

- [ ] All required commands passed without an unexplained difference.
- [ ] I inspected the acceptance predicates in `REVIEW_CHECKLIST.md` and the
      independent implementation boundary in `INDEPENDENT_CHECKS.md`.
- [ ] I confirm that this record and its attached transcript accurately report
      my replay.

Exceptions or observations:


Reviewer signature or verifiable signed-commit identifier:
