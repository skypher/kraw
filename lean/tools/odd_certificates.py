#!/usr/bin/env python3
"""Polynomial certificates for the odd-Q window lemma (paper Lemma 5.2).

Region of the transition u -> u+2 (Q >= 1, x = D - 2Q):
    u >= 1,  7(D+3) >= 30(u+3)^2,  X = x^2 in [Xmin2, Xmax],  Xmax = (D-2)^2,
    Xmin2 = (u+2)(u+4)(E-(u+3)^2)/(u+3)^2,  E = (D+3)^2.
Obligations (each must be >= 0 on the region):
    O1 = R1(Xmax), O2 = P1(Xmax), O3 = (u+3)^4 P1(Xmin2),
    O4 = (D+u+4)^2 (K^2 - disc2)/(u+2) at X = Xmax.
Each is certified by the substitution D = (30/7)(u+3)^2 - 3 + v, u = w + 1,
after which every coefficient in (w, v) is nonnegative.
Odd-D base: the cleared base polynomial factors as
(D+3)^2 (B_o^2 - g_1^2) = 4(D+1)(D+5)((D+3)^2 - (x-1)^2), nonnegative for
0 <= x <= D.

Usage: odd_certificates.py [--lean]   (--lean prints Lean-syntax polynomials)
"""
import sys

import sympy as sp


def lean_poly(expr, gens):
    """Print a polynomial with rational coefficients in Lean syntax."""
    poly = sp.Poly(sp.expand(expr), *gens)
    terms = []
    for monom, coeff in poly.terms():
        factors = []
        c = sp.Rational(coeff)
        if c.q != 1:
            factors.append(f"({c.p} / {c.q} : ℝ)")
        elif c != 1 or all(e == 0 for e in monom):
            factors.append(f"({c.p} : ℝ)")
        for g, e in zip(gens, monom):
            if e == 1:
                factors.append(str(g))
            elif e > 1:
                factors.append(f"{g} ^ {e}")
        terms.append(" * ".join(factors))
    return " + ".join(terms) if terms else "0"


def main():
    if any(a in ("-h", "--help") for a in sys.argv[1:]):
        print(__doc__)
        return 0
    lean = "--lean" in sys.argv[1:]
    D, x, u, v, w, X, g1 = sp.symbols('D x u v w X g1')
    E = (D + 3) ** 2

    def to_X(e):
        out = 0
        for (k,), c in sp.Poly(sp.expand(e), x).terms():
            assert k % 2 == 0
            out += c * X ** (k // 2)
        return sp.expand(out)

    disc1 = x**2*(u+1)**2 - u*(u+2)*(E-(u+1)**2)
    W1 = x*(u+1) + g1
    K = x*((u+1)*D + u**2 + 9*u + 12)/(D+u+4)
    B0 = u*(D-u)
    C0 = (u+2)*(D+u+6)
    disc2 = x**2*(u+3)**2 - (u+2)*(u+4)*(E-(u+3)**2)
    S1p = sp.Poly(sp.expand(((K*W1 - B0*C0)**2 - disc2*W1**2)*(D+u+4)**2), g1)
    P1 = sp.expand(sp.cancel(sp.expand(S1p.nth(0) + S1p.nth(2)*disc1)/(4*(u+2))))
    R1 = sp.expand(sp.cancel(sp.expand(S1p.nth(1))/(4*x*(u+2))))
    P1X, R1X = to_X(P1), to_X(R1)
    O4X = to_X(sp.expand(sp.cancel(sp.expand((K**2 - disc2)*(D+u+4)**2)/(u+2))))
    Xmax = (D - 2)**2
    Xmin2 = (u+2)*(u+4)*(E-(u+3)**2)/(u+3)**2
    print("P1(D,u,X) =", P1X if not lean else lean_poly(P1X, (D, u, X)))
    print("R1(D,u,X) =", R1X if not lean else lean_poly(R1X, (D, u, X)))
    print("O4X(D,u,X) =", O4X if not lean else lean_poly(O4X, (D, u, X)))
    obligations = {
        "O1": R1X.subs(X, Xmax),
        "O2": P1X.subs(X, Xmax),
        "O3": sp.together(P1X.subs(X, Xmin2))*(u+3)**4,
        "O4": O4X.subs(X, Xmax),
    }
    ok = True
    for name, T in obligations.items():
        T = sp.expand(sp.cancel(T))
        Ts = sp.expand(T.subs(D, sp.Rational(30, 7)*(u+3)**2 - 3 + v).subs(u, w + 1))
        poly = sp.Poly(Ts, w, v)
        neg = [c for _m, c in poly.terms() if c < 0]
        ok &= not neg
        print(f"{name}(D,u) =", T if not lean else lean_poly(T, (D, u)))
        print(f"{name} substituted ({len(poly.terms())} terms, negative={len(neg)}) =",
              Ts if not lean else lean_poly(Ts, (w, v)))
    Bo = (4*x + (D+1)*(D+5))/(D+3)
    Sodd = sp.expand(sp.cancel((Bo**2 - (x**2*4 - 3*(E-4)))*(D+3)**2))
    print("odd-D base S(D,x) =", Sodd if not lean else lean_poly(Sodd, (D, x)))
    good = sp.expand(Sodd - 4*(D+1)*(D+5)*((D+3)**2 - (x-1)**2)) == 0
    ok &= good
    print("base factorization (D+3)^2(B_o^2-g_1^2) = 4(D+1)(D+5)((D+3)^2-(x-1)^2):",
          good)
    print("ALL CERTIFICATES PASS" if ok else "CERTIFICATE FAILURE", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
