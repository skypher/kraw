#!/usr/bin/env python3
"""Deterministic, dependency-light interchange for exact certificates.

The producer scripts use SymPy to construct the polynomials.  The independent
C++ checker reads this deliberately simple text format without importing or
linking SymPy, GMP, or any computer-algebra library.
"""
import os

import sympy as sp


class WitnessWriter:
    def __init__(self, path, suite):
        self.path = path
        self.suite = suite
        self.blocks = [f"KRAW_WITNESS_V1 {suite}\n"]
        self.names = set()

    def poly(self, name, expr, variables):
        if name in self.names:
            raise RuntimeError(f"duplicate witness polynomial: {name}")
        if not name or any(ch.isspace() for ch in name):
            raise RuntimeError(f"invalid witness name: {name!r}")
        self.names.add(name)
        poly = sp.Poly(sp.expand(expr), *variables)
        terms = poly.terms()
        var_names = " ".join(str(var) for var in variables)
        self.blocks.append(
            f"POLY {name} {len(variables)} {var_names} {len(terms)}\n")
        for monomial, coeff in terms:
            coeff = sp.Rational(coeff)
            exponents = " ".join(str(value) for value in monomial)
            self.blocks.append(
                f"TERM {exponents} {int(coeff.p)} {int(coeff.q)}\n")
        return name

    def meta(self, kind, *fields):
        values = [str(field) for field in fields]
        if any(any(ch.isspace() for ch in value) for value in values):
            raise RuntimeError(
                f"whitespace is not permitted in META {kind}: {values}")
        self.blocks.append("META " + kind + " " + " ".join(values) + "\n")

    def finish(self):
        target = os.path.abspath(self.path)
        self._write_atomic(target, self.blocks + ["END\n"])
        partial = target + ".partial"
        if os.path.exists(partial):
            os.remove(partial)

    def checkpoint(self, label):
        """Persist all completed certificate blocks without claiming finality."""
        if not label or any(ch.isspace() for ch in label):
            raise RuntimeError(f"invalid checkpoint label: {label!r}")
        target = os.path.abspath(self.path) + ".partial"
        self._write_atomic(target, self.blocks + [f"CHECKPOINT {label}\n"])

    @staticmethod
    def _write_atomic(target, blocks):
        parent = os.path.dirname(target)
        os.makedirs(parent, exist_ok=True)
        temporary = target + ".tmp"
        with open(temporary, "w", encoding="ascii", newline="\n") as handle:
            handle.writelines(blocks)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, target)
