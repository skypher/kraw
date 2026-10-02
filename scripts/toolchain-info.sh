#!/usr/bin/env sh
# Print the versions of the tools used by the verification programs and the
# manuscript build.  Usage: toolchain-info.sh   (-h/--help prints this text)
set -eu
case "${1:-}" in -h|--help) sed -n '2,3p' "$0"; exit 0;; esac

python3 -u - <<'PY'
import platform
import sys
import sympy

print(f"python: {sys.version.split()[0]}")
print(f"python implementation: {platform.python_implementation()}")
print(f"sympy: {sympy.__version__}")
print(f"platform: {platform.platform()}")
PY

pdflatex --version | sed -n '1p'
