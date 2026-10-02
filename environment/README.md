# Locked replay environment

`Dockerfile` pins the multi-platform Ubuntu 24.04 image index by digest and
replaces the package sources with the Ubuntu snapshot dated 2026-08-25. Its
direct Python, TeX, and PDF-preflight packages are versioned; the Python
wheels are fixed by version and SHA-256 in `requirements.txt`.

From the repository root:

```sh
docker build -f environment/Dockerfile -t kraw-audit .
docker run --rm kraw-audit
docker run --rm kraw-audit make pdf-preflight
```

The default command is `make audit-fast`, which checks both manifests, prints
the toolchain, and replays all four verification programs against the
committed logs.  The Lean formalization is built separately with `make lean`.
