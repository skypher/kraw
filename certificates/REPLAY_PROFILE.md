# Complete replay profile retained for v1.0.4

This is the resource report for the complete proof replay prepared for release
`v1.0.3` and retained for `v1.0.4`.  Version `v1.0.4` adds the AI-use
disclosure and updates the manuscript version, release metadata, and
deterministic PDF source date; the proof generators, exact logs, dependencies,
and replay commands are unchanged.  This report supplements the deterministic
logs in this directory; it is not itself a proof certificate.

## Result

| Field | Value |
|---|---|
| Command | instrumented `make replay-all` stage sequence (exact command in the sanitized transcript) |
| Started | 2026-08-25 13:25:31 UTC |
| Finished | 2026-08-25 14:40:50 UTC |
| Exit status | `0` |
| Elapsed wall time | `1:15:18` |
| User CPU time | `5186.90 s` |
| System CPU time | `6.81 s` |
| Reported CPU utilization | `114%` |
| Maximum resident set | `338764 KiB` (about `331 MiB`) |
| Major page faults | `7` |
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

The recorded replay ran directly on the reference host with those versions,
`PYTHONHASHSEED=0`, `OMP_NUM_THREADS=24`, locale `C.UTF-8`, and time zone
`Etc/UTC`.  The machine-readable clean-room recipe in
`environment/Dockerfile` pins its Ubuntu base-image digest, dated Ubuntu
snapshot, system-package versions, and Python wheel hashes.

The wall time is a reproducibility datum rather than a benchmark. Machine
identity, account names, local paths, detailed host configuration, and shared
host activity are intentionally omitted from the public profile.

## Sanitized record and integrity boundary

The complete combined stdout/stderr and `/usr/bin/time -v` output prepared for
attachment to the versioned release has its working-directory path replaced
by `<repository-root>`.  The resulting file is named
`kraw-v1.0.4-replay-profile.sanitized.txt`; its SHA-256 digest is

```text
adf42bc7787846a2aad5217c6b1724eda5b4c86355840b67420a510f8213a8a8
```

This profile is included in `MANIFEST.sha256` but excluded from
`PAYLOAD.sha256`: timings and toolchain details are replay metadata, not part
of the stable noncircular proof-payload identifier printed in the manuscript.
