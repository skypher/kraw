# Complete replay profile for v1.0.2

This is the resource report for the complete proof replay shipped with release
`v1.0.2`. It supplements the deterministic logs in this directory; it is not
itself a proof certificate.

## Result

| Field | Value |
|---|---|
| Command | `make replay-profile` |
| Started | 2026-08-03 05:44:28 UTC |
| Finished | 2026-08-03 07:45:40 UTC |
| Exit status | `0` |
| Elapsed wall time | `2:01:11` |
| User CPU time | `7961.98 s` |
| System CPU time | `22.96 s` |
| Reported CPU utilization | `109%` |
| Maximum resident set | `924592 KiB` (about `903 MiB`) |
| Major page faults | `0` |
| Swaps | `0` |

Every replay stage passed:

- recurrence identities and the exact small scan;
- the regime decomposition and coverage checks;
- the `Q <= 2` small-argument certificates;
- the even- and odd-minimum gap verifiers;
- both parity certificates for every finite offset `u = 4,...,14`, with
  maximum regenerated onset `M0 = 153` and threshold `(4587,3,15)`;
- every fixed-argument strip `Q = 3,...,12`, with threshold
  `(14827,13,15)`;
- the GMP scan through `D = 1200`: `289261901` top-half cells, the asserted
  expected count, `576719000` checked exact divisions, and zero negatives.

## Reference toolchain

- Python `3.12.3` (CPython), SymPy `1.12`;
- g++ `13.3.0`, GMP `6.3.0`;
- pdfTeX `1.40.25` (TeX Live 2023/Debian).

The wall time is a reproducibility datum rather than a benchmark. Machine
identity, account names, local paths, detailed host configuration, and shared
host activity are intentionally omitted from the public profile.

## Sanitized record and integrity boundary

The immutable release attaches the complete combined stdout/stderr and
`/usr/bin/time -v` output with its working-directory path replaced by
`<repository-root>`, as
`kraw-v1.0.2-replay-profile.sanitized.txt`. Its SHA-256 digest is

```text
4535537ec2e08666ffc795bb7ec76ce886fc3a23a5aa1306f98b66079592b2fc
```

This profile is included in `MANIFEST.sha256` but excluded from
`PAYLOAD.sha256`: timings and toolchain details are replay metadata, not part
of the stable noncircular proof-payload identifier printed in the manuscript.
