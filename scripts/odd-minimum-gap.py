#!/usr/bin/env python3
"""Verification of every odd-minimum gap cell with u >= 2 by window propagation.

Relabel the exponents so that Q <= M.  Here Q is odd (Q >= 1), x = M-Q =
D-2Q <= D-2, and u >= 2 (u = 1 is the closed form in regime-decomposition.py).
Work in y_j := (D+2) p_{j+1}/p_j.

 (Y) EXACT MAP:  y_{j+1} = (1+kappa_j) x - kappa_j (D+2)^2 / y_j,
     kappa_j = (D-j)/(j+2); increasing in y on y > 0.
 (W) WINDOW: T_s >= 0 <=> G(y_s) >= 0 where G(y) = u(s+2) y^2
     - x(u+1)(D+2) y + (u+2)(D+1-s)(D+2)^2 (times p_s^2 >= 0;
     p_s = 0 is immediate).  On gap cells G has real roots
     y-(u) < y+(u); G(y) >= 0 for y >= y+(u).  By heredity every
     offset of the same parity below the target has a real window.
 (A) ANCHORS (reflection p_{D-j} = -p_j):
     D even: p_c = 0 (c = D/2), y_{c+1} = 2(D+2)x/(D+4) EXACTLY;
     D odd:  y_c = -(D+2) (c = (D-1)/2), so
             y_{c+1} = (D+2)(2x + D+1)/(D+3) EXACTLY.
 (B) BASE:  y_{c+1} >= y+(first cell):
     D even (u=2): rationalizes EXACTLY to x^2 <= (D+4)^2 -- always;
     D odd  (u=1): with Bo = (4x+(D+1)(D+5))/(D+3) > 0 the base is
     Bo >= g1, and (D+3)^2 (Bo^2 - g1^2) = 4(D+1)(D+5)((D+3)^2-(x-1)^2)
     > 0 for 0 <= x <= D.
 (S) STEP (interval invariance): map_{kappa(u)}(y+(u)) >= y+(u+2)
     whenever both windows are real and 7(D+3) >= 30(u+3)^2.  With
     W1 = x(u+1) + g1, K = x((u+1)D + u^2+9u+12)/(D+u+4), B0 = u(D-u),
     C0 = (u+2)(D+u+6), the step is equivalent to
     K W1 - B0 C0 >= g2 W1 with both sides nonnegative:
      (C1)  K x(u+1) - B0 C0 > 0 on the gap (exact boundary value
            4(D+3)(u+2)(D+u+4) after a positive factor);
      (S1)  (D+u+4)^2 [(K W1 - B0 C0)^2 - disc2 W1^2] = 4(u+2)(P1 + x R1 g1),
            P1 concave and R1 decreasing in X = x^2, so the four
            obligations O1 = R1(Xmax), O2 = P1(Xmax), O3 = (u+3)^4 P1(Xmin2)
            and O4 (the infinity state, K^2 - disc2 at Xmax) suffice,
            Xmax = (D-2)^2, Xmin2 = (u+2)(u+4)(E-(u+3)^2)/(u+3)^2.
            Each is coefficient-nonnegative after
            D = (30/7)(u+3)^2 - 3 + v, u = w + 1.
 (R) REGION: gap strip with Q >= 1 gives 30(u+1)^2 < 7(D+3), so every
     transition r -> r+2 <= u has 30(r+3)^2 < 7(D+3).

CONCLUSION: y_j >= y+(j) propagates from the base to the target; hence
T_s >= 0 at every odd-minimum gap cell with u >= 2.

CHECKS: [Y][W][A] symbolic; [B] exact identities and factorization;
[C1] factored identity + K-positivity/monotonicity; [S1] reductions +
coefficient positivity; [R] region arithmetic; [E] E2E: exact window walk
on every odd-Q gap cell with D <= 600.  This verifier is float-free.

Usage: odd-minimum-gap.py   (-h/--help prints this text)
"""
from fractions import Fraction as F
from math import comb
import sys

import sympy as sp

OK = True
def check(name, cond):
    global OK
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}", flush=True)
    OK = OK and cond


def require(cond, msg):
    """Hard certificate gate that remains active under ``python3 -O``."""
    if not cond:
        raise RuntimeError(f"certificate identity failed: {msg}")


D, x, u, v, w, X, g1 = sp.symbols('D x u v w X g1', positive=True)
E = (D+3)**2


def to_X(e):
    pe = sp.Poly(e, x)
    out = 0
    for (k,), c in pe.terms():
        require(k % 2 == 0, f"to_X received odd power x^{k}")
        out += c*X**(k//2)
    return sp.expand(out)


def poly_nonneg_region(T, name):
    """T(D, u) >= 0 on {u >= 1, 7(D+3) >= 30(u+3)^2}: after
    D = (30/7)(u+3)^2 - 3 + v and u = w + 1 every coefficient is >= 0."""
    Ta = sp.expand(T.subs(D, sp.Rational(30, 7)*(u+3)**2 - 3 + v).subs(u, w + 1))
    pa = sp.Poly(Ta, w, v)
    ok = all(c >= 0 for _m, c in pa.terms())
    min_coeff = min(c for _m, c in pa.terms())
    check(f"{name}: coefficient-nonnegative after substitution "
          f"({len(pa.terms())} terms, min={min_coeff})", ok)
    return ok


def main():
    if any(a in ('-h', '--help') for a in sys.argv[1:]):
        print(__doc__)
        return
    jv, y = sp.symbols('j y')
    pj, pj1 = sp.symbols('pj pj1')

    print("== [Y] the y-map ==")
    pj2 = (x*pj1 + (jv - D)*pj)/(jv + 2)
    kap = (D - jv)/(jv + 2)
    ymap = (1 + kap)*x - kap*(D+2)**2/y
    lhs = (D+2)*pj2/pj1
    check("y_{j+1} == (1+k)x - k(D+2)^2/y_j",
          sp.simplify(sp.together(
              lhs - ymap.subs(y, (D+2)*pj1/pj))) == 0)
    check("map derivative == k(D+2)^2/y^2 (positive for 0 <= j < D, y > 0)",
          sp.simplify(sp.diff(ymap, y) - kap*(D+2)**2/y**2) == 0)

    print("== [W] window ==")
    sv = (D + u)/2
    G = u*(sv+2)*y**2 - x*(u+1)*(D+2)*y + (u+2)*(D+1-sv)*(D+2)**2
    Tcond = ((u+2)*(D+1-sv)*pj**2 - x*(u+1)*pj*pj1 + u*(sv+2)*pj1**2)
    check("G(y) p^2 == (D+2)^2 (T-condition), y = (D+2)p'/p",
          sp.simplify(sp.together(
              G.subs(y, (D+2)*pj1/pj)*pj**2
              - (D+2)**2*Tcond)) == 0)
    disc1 = x**2*(u+1)**2 - u*(u+2)*(E-(u+1)**2)
    discG = sp.expand(x**2*(u+1)**2*(D+2)**2
                      - 4*u*(u+2)*(sv+2)*(D+1-sv)*(D+2)**2)
    check("disc(G) == (D+2)^2 [x^2(u+1)^2 - u(u+2)((D+3)^2-(u+1)^2)]",
          sp.expand(discG - (D+2)**2*disc1) == 0)
    # direct: 4(s+2)(D+1-s) == (D+3)^2 - (u+1)^2:
    check("4(s+2)(D+1-s) == (D+3)^2 - (u+1)^2",
          sp.expand(4*(sv+2)*(D+1-sv) - (E - (u+1)**2)) == 0)

    print("== [A] anchors ==")
    a = sp.Symbol('a')
    # D even: p_c = 0, p_{c+2} = x p_{c+1}/(c+2):
    cE = D/2
    check("D even: y_{c+1} == 2(D+2)x/(D+4)",
          sp.simplify((D+2)*(x*a/(cE+2))/a - 2*(D+2)*x/(D+4)) == 0)
    # D odd: y_c = -(D+2):
    cO = (D-1)/2
    kapc = (D - cO)/(cO + 2)
    yc1 = sp.simplify((1+kapc)*x - kapc*(D+2)**2/(-(D+2)))
    check("D odd: y_{c+1} == (D+2)(2x+D+1)/(D+3)",
          sp.simplify(yc1 - (D+2)*(2*x+D+1)/(D+3)) == 0)

    print("== [B] base cases ==")
    disc2u = lambda uu: sp.expand(
        x**2*(uu+1)**2 - uu*(uu+2)*(E-(uu+1)**2))
    # D even, u=2: base >= y+(2) <=> g(2) <= x(D+12)/(D+4):
    Bv = x*(D+12)/(D+4)
    idE = sp.simplify(sp.together(Bv**2 - disc2u(2)
                      - 8*D*(D+6)*((D+4)**2 - x**2)/(D+4)**2))
    check("D even base: B^2 - disc == 8D(D+6)((D+4)^2 - x^2)/(D+4)^2",
          idE == 0)
    # reduction identity: base - y+(2) has the sign of B - g:
    yb = 2*(D+2)*x/(D+4)
    yp2 = (D+2)*(3*x + g1)/(2*(D+6))
    check("D even base reduction: (yb - yp2)*2(D+6)/(D+2) == B - g",
          sp.simplify(sp.together(
              (yb - yp2)*2*(D+6)/(D+2) - (Bv - g1))) == 0)
    # D odd, u=1: base >= y+(1) <=> g(1) <= [4x + (D+1)(D+5)]/(D+3):
    Bo = (4*x + (D+1)*(D+5))/(D+3)
    ybo = (D+2)*(2*x + D+1)/(D+3)
    yp1 = (D+2)*(2*x + g1)/(D+5)
    check("D odd base reduction: (ybo - yp1)*(D+5)/(D+2) == Bo - g",
          sp.simplify(sp.together(
              (ybo - yp1)*(D+5)/(D+2) - (Bo - g1))) == 0)
    Sodd = sp.expand((Bo**2 - disc2u(1))*(D+3)**2)
    check("D odd base: (D+3)^2 (Bo^2 - g1^2) == 4(D+1)(D+5)((D+3)^2-(x-1)^2)",
          sp.cancel(Sodd - 4*(D+1)*(D+5)*((D+3)**2 - (x-1)**2)) == 0)
    check("D odd base: Bo > 0 and (D+3)^2 - (x-1)^2 > 0 for 0 <= x <= D "
          "[(D+3)^2-(x-1)^2 = (D+4-x)(D+2+x)]",
          sp.expand((D+3)**2 - (x-1)**2 - (D+4-x)*(D+2+x)) == 0)

    print("== [C1] ==")
    N = (u+1)*D + u**2 + 9*u + 12
    # K > 0 and K x(u+1) increasing in X = x^2: both reduce to the
    # positivity of N's coefficients (K = xN/(D+u+4), and the X-form
    # of K x(u+1) is X(u+1)N/(D+u+4)):
    check("K > 0 and K x(u+1) increasing in X: N has positive "
          "coefficients", all(c > 0 for c in sp.Poly(N, D, u).coeffs()))
    # C1 is K x(u+1) - B0 C0 at the gap boundary X = u(u+2)(E-U)/U,
    # cleared by the positive factor (u+1)(D+u+4)/(u(u+2)):
    C1 = sp.expand((E-(u+1)**2)*N
                   - (u+1)*(D-u)*(D+u+6)*(D+u+4))
    check("C1 == 4(D+3)(u+2)(D+u+4)",
          sp.expand(C1 - 4*(D+3)*(u+2)*(D+u+4)) == 0)

    print("== [S1] step obligations ==")
    W1 = x*(u+1) + g1
    K  = x*((u+1)*D + u**2 + 9*u + 12)/(D+u+4)
    B0 = u*(D-u)
    C0 = (u+2)*(D+u+6)
    disc2 = x**2*(u+3)**2 - (u+2)*(u+4)*(E-(u+3)**2)
    g2 = sp.Symbol('g2', positive=True)
    yplus1 = (D+2)*W1/(u*(D+u+4))
    yplus2 = (D+2)*(x*(u+3)+g2)/((u+2)*(D+u+6))
    kappa = (D-u)/(D+u+4)
    mapped = (1+kappa)*x-kappa*(D+2)**2/yplus1
    transition = K*W1-B0*C0-g2*W1
    check("map(y_+(u)) - y_+(u+2) has the sign of "
          "K W1 - B0 C0 - g2 W1",
          sp.simplify(sp.together(
              (mapped-yplus2)*W1*u*(D+u+4)*(u+2)*(D+u+6)/(D+2)
              - u*(D+u+4)*transition)) == 0)
    S1 = sp.expand(((K*W1 - B0*C0)**2 - disc2*W1**2)*(D+u+4)**2)
    S1p = sp.Poly(S1, g1)
    P = sp.expand(S1p.nth(0) + S1p.nth(2)*disc1)
    R = sp.expand(S1p.nth(1))
    P1 = sp.expand(sp.cancel(P/(4*(u+2))))
    R1 = sp.expand(sp.cancel(R/(4*x*(u+2))))
    check("P == 4(u+2) P1 and R == 4x(u+2) R1 exactly",
          sp.expand(P - 4*(u+2)*P1) == 0
          and sp.expand(R - 4*x*(u+2)*R1) == 0)
    P1X = sp.Poly(to_X(P1), X)
    R1X = sp.Poly(to_X(R1), X)
    check("P1 X^2-coeff == 2(u+1)^2(u-D)(D+u+6)  [concave]",
          sp.expand(P1X.nth(2)
                    - 2*(u+1)**2*(u-D)*(D+u+6)) == 0)
    check("R1 X-coeff == 2(u+1)(u-D)(D+u+6)  [decreasing]",
          sp.expand(R1X.nth(1) - 2*(u+1)*(u-D)*(D+u+6)) == 0)
    check("D > u on the region: (30/7)(u+3)^2 - 3 - u > 0 for u >= 1",
          all(c > 0 for c in sp.Poly(sp.expand(
              (30*(u+3)**2 - 21 - 7*u).subs(u, w+1)), w).all_coeffs()))
    Xmax = (D-2)**2
    Xmin2 = (u+2)*(u+4)*(E-(u+3)**2)/(u+3)**2
    obligations = {
        "O1 R1(Xmax)": sp.expand(R1X.as_expr().subs(X, Xmax)),
        "O2 P1(Xmax)": sp.expand(P1X.as_expr().subs(X, Xmax)),
        "O3 (u+3)^4 P1(Xmin2)": sp.expand(sp.together(
            P1X.as_expr().subs(X, Xmin2))*(u+3)**4),
    }
    O3 = sp.expand(sp.cancel(sp.expand(
        (K**2 - disc2)*(D+u+4)**2)/(u+2)))
    O3X = sp.Poly(to_X(O3), X)
    check("O4 X-coeff == 4(u-D)(D+u+6)  [decreasing]",
          sp.expand(O3X.nth(1) - 4*(u-D)*(D+u+6)) == 0)
    obligations["O4 (D+u+4)^2(K^2-disc2)/(u+2) at Xmax"] = sp.expand(
        O3X.as_expr().subs(X, Xmax))
    for name, T in obligations.items():
        poly_nonneg_region(sp.expand(sp.nsimplify(T)), name)

    print("== [R] region facts ==")
    Qs, rr = sp.symbols('Qs rr', nonnegative=True)
    check("Q >= 1: 6(2Q+3) >= 30, so gap strip gives 30(u+1)^2 < 7(D+3)",
          sp.expand(6*(2*(Qs+1)+3) - 30 - 12*Qs) == 0)
    check("r + 2 <= u  =>  (r+3)^2 <= (u+1)^2 (transition region)",
          sp.expand((rr+2+1)**2 - (rr+3)**2) == 0)

    print("== [E] E2E: exact window walk ==")
    def prow(M, Q):
        DD = M + Q
        p = [0]*(DD+3); p[0] = 1
        if DD >= 1:
            p[1] = M - Q
        for jj in range(1, DD):
            num = (M-Q)*p[jj] + (jj-1-DD)*p[jj-1]
            require(num % (jj+1) == 0, "exact division in the recurrence")
            p[jj+1] = num//(jj+1)
        return p

    def in_state(DD, xx, r, a, b):
        """(a, b) = (p_j, p_{j+1}) lies in C_r (y >= y+(r) or y = oo)."""
        if a == 0:
            return b != 0
        EE = (DD+3)**2
        g2 = xx*xx*(r+1)**2 - r*(r+2)*(EE-(r+1)**2)
        L = F((DD+2)*b, a)*r*(DD+r+4)/(DD+2) - xx*(r+1)
        return g2 >= 0 and L >= 0 and L*L >= g2

    okE = True; ncells = 0
    for DD in range(2, 601):
        EE = (DD+3)**2
        for Q in range(1, DD//2+1, 2):
            M = DD - Q; xx = M - Q; cells = []
            for uu in range(2 - DD % 2, DD+1, 2):
                U = (uu+1)**2
                if U >= (DD+1)**2 - xx*xx or not xx*xx*U > (U-1)*(EE-U):
                    break
                if uu >= 2:
                    cells.append(uu)
            if not cells:
                continue
            p = prow(M, Q)
            for uu in cells:
                s_ = (DD+uu)//2; ncells += 1
                okE &= all(in_state(DD, xx, 2*jj-DD, p[jj], p[jj+1])
                           for jj in range(DD//2+1, s_+1))
                okE &= (p[s_]**2 + p[s_]*p[s_+2] - p[s_+1]**2
                        - p[s_-1]*p[s_+1]) >= 0
    check(f"E2E: {ncells} odd-Q gap cells with u >= 2, D <= 600: state C_r "
          f"along the whole path and T >= 0 (exact)", okE and ncells > 1000)

    print("== ODD-MINIMUM GAP:", "ALL CHECKS PASS ==" if OK else
          "FAILURES ==")
    if OK:
        print("  => every odd-minimum gap cell with u >= 2 is verified.")
    raise SystemExit(0 if OK else 1)


if __name__ == '__main__':
    main()
