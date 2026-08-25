# Locked replay environment

`Dockerfile` pins the multi-platform Ubuntu 24.04 image index by digest and
replaces the package sources with the Ubuntu snapshot dated 2026-08-25. Its
direct compiler, GMP, Python, TeX, and PDF-preflight packages are versioned;
the Python wheels are fixed by version and SHA-256 in `requirements.txt`.

From the repository root:

```sh
docker build -f environment/Dockerfile -t kraw-audit .
docker run --rm kraw-audit
```

The default command is `make audit-fast`. For the complete replay and PDF
preflight:

```sh
docker run --rm kraw-audit make replay-profile
docker run --rm kraw-audit make pdf-preflight
```

The complete replay is intentionally not part of routine CI because of its
runtime. A release profile must record the resulting image ID, toolchain
report, wall time, peak memory, and exit status.
