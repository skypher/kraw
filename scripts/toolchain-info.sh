#!/usr/bin/env sh
set -eu

python3 - <<'PY'
import platform
import sys
import sympy

print(f"python: {sys.version.split()[0]}")
print(f"python implementation: {platform.python_implementation()}")
print(f"sympy: {sympy.__version__}")
print(f"platform: {platform.platform()}")
PY

g++ --version | sed -n '1p'
pkg-config --modversion gmp | sed 's/^/gmp: /'
pdflatex --version | sed -n '1p'
