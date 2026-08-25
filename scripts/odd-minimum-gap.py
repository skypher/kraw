#!/usr/bin/env python3
"""Verification of every odd-minimum gap cell by interval invariance.

Relabel the exponents so that Q <= M. Here Q is odd (both D parities), Q >= 13,
D >= 14827, x = M-Q,
gap cells.  Work in y_j := (D+2) p_{j+1}/p_j.

The ingredients below are checked symbolically:

 (Y) EXACT MAP:  y_{j+1} = (1+kappa_j) x - kappa_j (D+2)^2 / y_j,
     kappa_j = (D-j)/(j+2); increasing in y on y > 0.
 (W) WINDOW: T_s >= 0 <=> G(y_s) >= 0 where G(y) = u(s+2) y^2
     - x(u+1)(D+2) y + (u+2)(D+1-s)(D+2)^2 (times p_s^2 >= 0;
     p_s = 0 is immediate).  On gap cells G has real roots
     y-(u) < y+(u); G(y) >= 0 for y >= y+(u).  The gap is
     downward-closed in u, so every even (odd) u below the target
     has a window for D even (odd).
 (A) ANCHORS (reflection p_{D-j} = -p_j):
     D even: p_c = 0 (c = D/2), y_{c+1} = 2(D+2)x/(D+4) EXACTLY;
     D odd:  y_c = -(D+2) (c = (D-1)/2), so
             y_{c+1} = (1+kappa_c) x + kappa_c (D+2)
                     = (D+2)(2x + D+1)/(D+3) EXACTLY.
 (B) BASE:  y_{c+1} >= y+(first cell):
     D even (u=2):  rationalizes EXACTLY to x^2 <= (D+4)^2 — always;
     D odd  (u=1):  rationalizes to a quadratic in x with negative
     x^2-coefficient — the coefficient is checked exactly and endpoint
     nonnegativity on 16(D+3)/17 <= x <= D-26 is certified by
     coefficient positivity (with an exact Sturm fallback available).
 (S) STEP (interval invariance): map_{kappa(u)}(y+(u)) >= y+(u+2),
     for every u >= 1 with both windows real.  Proof: with
     W1 = x(u+1) + g1, K = x((u+1)D + u^2+9u+12)/(D+u+4),
     B0 = u(D-u), C0 = (u+2)(D+u+6), the step is equivalent to
     K W1 - B0 C0 >= g2 W1 with both sides nonnegative:
      (C1)  K x(u+1) - B0 C0 >= 0 on the gap: K x(u+1) is increasing
            in X = x^2 (numerator N = (u+1)D + u^2+9u+12 has positive
            coefficients, which also gives K > 0 -- both machine-
            checked), and substituting the gap lower bound on x^2 and
            clearing the positive factor (u+1)(D+u+4)/(u(u+2)) leaves
            the EXACT positive value 4(D+3)(u+2)(D+u+4);
      (S1)  (D+u+4)^2 [(K W1 - B0 C0)^2 - disc2 W1^2] = P + R g1
            (K's denominator cleared by the positive square
            (D+u+4)^2, matching the manuscript's display) with
            P = 4(u+2) P1, R = 4x(u+2) R1, and (in X = x^2):
            P1 is CONCAVE in X (X^2-coeff 2(u+1)^2(u-D)(D+u+6)
            <= 0) and R1 is linear with negative slope
            2(u+1)(u-D)(D+u+6), so both are minimized at the
            X-interval endpoints  Xmin2 = (u+2)(u+4)(E-(u+3)^2)
            /(u+3)^2  (disc2 >= 0)  and  Xmax = (D-26)^2 (Q >= 13);
            the FOUR endpoint polynomials are nonnegative on
            {u >= 1, 24 u^2 <= D+3, D >= 14827}: substituting
            D = 24u^2 - 3 + v and u -> w + 25 makes ALL coefficients
            nonnegative (u >= 25), and the strip u = 1..24 with
            D = 14827 + v is per-u coefficient/Sturm positive.
 (I) INFINITY PASS-THROUGH: if p_j = 0 (y = oo), the next value is
     (1+kappa)x and (1+kappa)x >= y+(u+2) <=> K^2 >= disc2, whose
     X-form is linear with negative slope 4(u-D)(D+u+6) —
     certified at Xmax by the same coefficient-positivity method.
 (R) REGION: gap + Q >= 13 => (u+1)^2 <= (7/6)(D+3)/29 =>
     24 u^2 <= (168/174)(D+3) <= D+3;  x <= D-26;  and
     x^2 > (8/9)(E-(u+1)^2) => 17x > 16(D+3), replayed through the
     manuscript's own chain: (1-1/U) >= 255/256 >= 8/9 (U >= 256),
     the identity (8/9)(E-(D+3)/24) = E(24(D+3)-1)/(27(D+3)), and
     the equivalence ... >= E(256/289) <=> 24(D+3) >= 289, each
     symbolic or coefficient-certified on the ray D >= 14827.

CONCLUSION: y_j >= y+(j) propagates from the base through the whole
strip; hence T_s >= 0 at every odd-minimum gap cell.

CHECKS: [Y][W][A] symbolic; [B] exact identity + Sturm; [C1]
factored identity + K-positivity/monotonicity; [S1] endpoint
reductions + coefficient positivity + strip Sturm; [I] same; [R] the
manuscript's arithmetic chain, symbolic/ray-certified; [E] E2E: exact
recurrence walk on both-parity odd-min cells at D ~ 14828+ vs binomial
p-values.  This verifier is float-free: every check is exact.
"""
from fractions import Fraction as F
from math import comb

import sympy as sp

OK = True
def check(name, cond):
    global OK
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}", flush=True)
    OK = OK and cond


D, x, u, v, w, X, g1 = sp.symbols('D x u v w X g1', positive=True)
E = (D+3)**2


def to_X(e):
    pe = sp.Poly(e, x)
    out = 0
    for (k,), c in pe.terms():
        assert k % 2 == 0
        out += c*X**(k//2)
    return sp.expand(out)


def poly_nonneg_region(T, name, ulo=1):
    """T(D, u) >= 0 on {u >= ulo, 24u^2 <= D+3, D >= 14827}."""
    okA = True
    Ta = sp.expand(T.subs(D, 24*u**2 - 3 + v).subs(u, w + 25))
    pa = sp.Poly(Ta, w, v)
    nega = [(m, c) for m, c in pa.terms() if c < 0]
    min_coeff = min(c for _m, c in pa.terms())
    if nega:
        okA = False
    okB = True
    sturm_used = []
    for u0 in range(ulo, 25):
        Tb = sp.expand(T.subs(u, u0).subs(D, 14827 + v))
        pb = sp.Poly(Tb, v)
        if any(c < 0 for c in pb.all_coeffs()):
            sturm_used.append((u0, pb.degree()))
            if (pb.LC() <= 0 or pb.count_roots(0, sp.oo) != 0
                    or pb.eval(0) <= 0):
                okB = False
    check(f"{name}: u>=25 all-coeffs>=0 ({len(pa.terms())} terms, "
          f"min={min_coeff}); strip u={ulo}..24 "
          f"(Sturm fallbacks={sturm_used})", okA and okB)
    return okA and okB


def main():
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
    pS = sp.Poly(Sodd, x)
    # Concavity must hold on the whole D-domain; checking only the leading
    # coefficient of this polynomial in D would not certify that.
    check("D odd base: x^2-coeff == -4(D+1)(D+5) < 0",
          sp.expand(pS.nth(2) + 4*(D+1)*(D+5)) == 0)
    okoddbase = True
    for xe in (16*(D+3)/17, D-26):
        Te = sp.together(Sodd.subs(x, xe))
        num, den = sp.fraction(sp.cancel(Te))
        # the denominator must be CERTIFIED positive (a positive
        # constant or all-positive coefficients in D); anything else
        # is a FAIL -- never silently patched:
        dp = sp.Poly(sp.expand(den), D)
        okden = ((den.is_number and den > 0)
                 or (dp.degree() >= 0
                     and all(c > 0 for c in dp.all_coeffs())))
        pb = sp.Poly(sp.expand(sp.expand(num).subs(D, 14827+v)), v)
        okx = okden and (all(c >= 0 for c in pb.all_coeffs())
               or (pb.LC() > 0 and pb.count_roots(0, sp.oo) == 0
                   and pb.eval(0) > 0))
        okoddbase &= okx
    check("D odd base: nonneg at both x-endpoints (D >= 14827)",
          okoddbase)

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
    check("D > u on the remaining region",
          all(c > 0 for c in sp.Poly(
              (24*u**2 - 3 - u).subs(u, w+1), w).all_coeffs()))
    Xmax = (D-26)**2
    Xmin2 = (u+2)*(u+4)*(E-(u+3)**2)/(u+3)**2
    obligations = {
        "O1' R1(Xmax)": sp.expand(R1X.as_expr().subs(X, Xmax)),
        "O2a P1(Xmax)": sp.expand(P1X.as_expr().subs(X, Xmax)),
        "O2b P1(Xmin2)(u+3)^4": sp.expand(sp.together(
            P1X.as_expr().subs(X, Xmin2))*(u+3)**4),
    }
    O3 = sp.expand(sp.cancel(sp.expand(
        (K**2 - disc2)*(D+u+4)**2)/(u+2)))
    O3X = sp.Poly(to_X(O3), X)
    check("O3 X-coeff == 4(u-D)(D+u+6)  [decreasing]",
          sp.expand(O3X.nth(1) - 4*(u-D)*(D+u+6)) == 0)
    obligations["O3' O3(Xmax)"] = sp.expand(
        O3X.as_expr().subs(X, Xmax))
    for name, T in obligations.items():
        poly_nonneg_region(sp.expand(sp.nsimplify(T)), name, ulo=1)

    print("== [R] region facts ==")
    check("(u+1)^2 <= (7/6)(D+3)/29 => 24u^2 <= D+3  (168 <= 174)",
          F(24*7, 6*29) <= 1)
    # the manuscript's chain for 17x > 16(D+3), step by step:
    check("U >= 256 => 1 - 1/U >= 255/256 >= 8/9",
          F(255, 256) >= F(8, 9))
    check("(8/9)(E - (D+3)/24) == E(24(D+3)-1)/(27(D+3))  (identity)",
          sp.simplify(sp.together(
              sp.Rational(8, 9)*(E - (D+3)/sp.Integer(24))
              - E*(24*(D+3)-1)/(27*(D+3)))) == 0)
    # E(24(D+3)-1)/(27(D+3)) >= E(256/289) <=> 24(D+3) >= 289,
    # certified on the whole ray D >= 14827:
    check("289(24(D+3)-1) - 6912(D+3) == 24(D+3)-289  (identity)",
          sp.expand(289*(24*(D+3)-1) - 256*27*(D+3)
                    - (24*(D+3)-289)) == 0)
    check("24(D+3)-289 > 0 for all D >= 14827 (ray certificate)",
          all(c > 0 for c in sp.Poly(
              sp.expand((24*(D+3)-289).subs(D, 14827+v)),
              v).all_coeffs()))

    print("== [E] E2E: exact recurrence walk ==")
    def pcoef(M, Q):
        DD = M + Q
        row = [0]*(M+1)
        b = 1
        for i in range(M+1):
            row[i] = b
            b = b*(M-i)//(i+1)
        p = [0]*(DD+1)
        for jj in range(Q+1):
            cq = comb(Q, jj)*(-1)**(Q-jj)
            for i in range(M+1):
                p[i+jj] += cq*row[i]
        return p

    okE = True; ncells = 0
    for (M, Q) in [(14815, 13), (14814, 13), (14816, 13),
                   (14801, 27), (14800, 27)]:
        DD = M + Q; xx = M - Q
        if Q % 2 == 0: continue
        p = pcoef(M, Q)
        EE = (DD+3)**2
        c = DD//2; delta = DD % 2
        for uu in range(2 - delta, 300, 2):
            U = (uu+1)**2
            if not (U < (DD+1)**2 - xx*xx
                    and xx*xx*U > (U-1)*(EE-U)):
                continue
            s = (DD+uu)//2
            ncells += 1
            # T >= 0 and y >= y+ numerically at the cell:
            T = (p[s]**2 + p[s]*p[s+2] - p[s+1]**2 - p[s-1]*p[s+1])
            if T < 0: okE = False
            d1 = xx*xx*(uu+1)**2 - uu*(uu+2)*(EE-(uu+1)**2)
            if p[s] != 0 and d1 >= 0:
                # y >= y+ <=> yv*u(D+u+4) - (D+2)x(u+1) >= (D+2)sqrt(d1)
                # exact integer comparison via squaring:
                lhsr = (F((DD+2)*p[s+1], p[s])*uu*(DD+uu+4)
                        - (DD+2)*xx*(uu+1))
                rhs2 = (DD+2)**2*d1
                if lhsr < 0 or lhsr*lhsr < rhs2:
                    okE = False
    check(f"E2E: {ncells} odd-min gap cells at D ~ 14828: T >= 0 "
          f"and orbit above window", okE and ncells > 20)

    print("== ODD-MINIMUM GAP:", "ALL CHECKS PASS ==" if OK else
          "FAILURES ==")
    if OK:
        print("  => every odd-minimum gap cell is verified.")
    raise SystemExit(0 if OK else 1)


if __name__ == '__main__':
    main()
