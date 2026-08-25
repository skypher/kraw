#!/usr/bin/env python3
"""Exact verification for min(M,Q) <= 2 at every D.

WLOG x = M-Q >= 0.  For fixed Q the values
p_{s+j} are Q+1-term sums of binomials; normalizing by C(M, s)^2 and
substituting s = (D+u)/2, M = D-Q collapses T_s to an EXACT rational
form  T_s = c * N_Q(u, D) / A_Q(u, D)  valid wherever the interposed
binomial ratios are finite (u <= D - 10 covers all uses below); the
denominator A_Q < 0 on u <= D-10 after orienting, and:

  Q = 0:  N_0 = -(D+1)(D+2)(1+u)                 < 0  => T > 0.
  Q = 1:  N_1 = -D(D+1) u (u+1)(u+2)             <= 0 => T >= 0
          (equality exactly at u = 0 for Q odd).
  Q = 2:  N_2 = -D(D-1) S_2(u, D),  S_2 = c0 + c1 u + c2 u^2 + c3 u^3
          + c4 u^4 + c5 u^5 with c0, c1, c4, c5 >= 0 and c2, c3 <= 0
          (c_j the coefficients of S_2 itself);
          on the strip  u^2 <= D/13  paired domination closes it:
            13 c0 + D c2 = D(33D + 70)          >= 0   [i]
            13 c1 + D c3 = 37D^2 + 30D - 104    >= 0   [ii]  (D >= 2)
          so S_2 >= (c0 + c2 u^2) + u (c1 + c3 u^2) + c4 u^4 >= 0.

  STRIP >= GAP (Q = 2): on the gap, U = (u+1)^2 < U- and, using
  h >= 2 sqrt(E) (certified: h - 2(D+3) = 12D - 12 >= 0 for D >= 1),
  U- <= E/(h - sqrt(E)) with h = E+1-x^2 = 14D - 6, sqrt(E) = D+3:
  (u+1)^2 <= (D+3)^2/(13D-9) <= D/13 + 1 for D >= 3, because
  13(D+3)^2 - D(13D-9) = 87D + 117 and 13(13D-9) - (87D+117)
  = 82D - 234 >= 0 for D >= 3; hence u^2 <= D/13.  Cells OUTSIDE the
  strip are outside the gap and covered by the bulk/flow
  decomposition; cells with u > D-10 have v = D-u < 10, i.e.
  k = (D-u)/2 <= 4, and are flow-covered for D >= 24: all twelve
  combinations (D-2Q)^2 >= 4k(D+1-k), Q <= 2, 1 <= k <= 4, are
  certified by coefficient positivity after D = 24 + r; everything
  with D <= 1200 is scan-covered and independently re-verified here
  on a grid.

CHECKS (exact):
[I]  the three rational identities, symbolically (sympy, exact) and
     numerically against binomial p-values on a grid.
[P]  positivity structure: N_0, N_1 coefficient signs; Q = 2 paired
     domination identities [i], [ii] in factored form; c4, c5 >= 0;
     denominator orientation AND square-factor nonvanishing on the
     domain u <= D-10 actually used by the proof.
[G]  strip >= gap algebra, every quantified step certified on its
     full ray by coefficient positivity (not spot values): the two
     identities above, 82D-234 >= 0 (D >= 3), 13D-9 > 0 (D >= 1),
     h >= 2 sqrt(E) (D >= 1), 37D^2+30D-104 > 0 (D >= 2), and the
     twelve edge-flow inequalities (D >= 24).
[E]  E2E grid: for all D <= 140, Q <= 2, every top-half cell is
     covered by {identity-region positivity} u {flow at the edge} u
     {direct value check}, T >= 0 throughout, and every direct-only
     cell has D < 24 (scan-covered), asserted rather than assumed.
"""
from math import comb

import sympy as sp

OK = True
def check(name, cond):
    global OK
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}", flush=True)
    OK = OK and cond


Dv, uv = sp.symbols('D u')
Mv, sv = sp.symbols('M s')


def strip_form(Q):
    """exact rational form of T for fixed Q: (num, den) in (u, D),
    T = num/den wherever the binomial ratios are finite."""
    def prat(j):
        tot = 0
        for b_ in range(Q+1):
            d = j - b_
            r = sp.Integer(1)
            if d >= 0:
                for i in range(d):
                    r *= (Mv - sv - i)/(sv + i + 1)
            else:
                for i in range(-d):
                    r *= (sv - i)/(Mv - sv + i + 1)
            tot += (-1)**b_*sp.binomial(Q, b_)*r
        return sp.together(tot)
    T = sp.together(prat(0)**2 + prat(0)*prat(2) - prat(1)**2
                    - prat(-1)*prat(1))
    num, den = sp.fraction(sp.cancel(T))
    num = sp.expand(num.subs({sv: (Dv+uv)/2, Mv: Dv-Q}))
    den = sp.together(den.subs({sv: (Dv+uv)/2, Mv: Dv-Q}))
    return num, den


def pcoef(M, Q):
    D = M + Q
    p = [0]*(D+1)
    for i in range(M+1):
        for j in range(Q+1):
            p[i+j] += comb(M, i)*comb(Q, j)*(-1)**(Q-j)
    return p


def Tval(p, D, Q, s):
    def pv(j):
        return p[j] if 0 <= j <= D else 0
    return pv(s)**2 + pv(s)*pv(s+2) - pv(s+1)**2 - pv(s-1)*pv(s+1)


def main():
    print("== [I] exact rational identities ==")
    forms = {}
    preds = {
        0: -(Dv+1)*(Dv+2)*(1+uv),
        1: -Dv*(Dv+1)*uv*(uv+1)*(uv+2),
    }
    for Q in (0, 1, 2):
        num, den = strip_form(Q)
        forms[Q] = (num, den)
        if Q in preds:
            # num == const * pred with const > 0
            ratio = sp.cancel(num/preds[Q])
            check(f"Q={Q}: numerator == c * closed form, c = {ratio} > 0",
                  ratio.is_number and ratio > 0)
    # numeric verification of T == (num/den) * C(M,s)^2 (u <= D-10)
    ok = True
    for Q in (0, 1, 2):
        num, den = forms[Q]
        ratio = sp.cancel(num/den)
        for M in range(Q+12, 61, 7):
            D = M + Q
            p = pcoef(M, Q)
            for s in range((D+1)//2, D-4):
                u = 2*s-D
                if u > D-10: continue
                lhs = Tval(p, D, Q, s)
                rhs = ratio.subs({uv: u, Dv: D})*comb(M, s)**2
                ok &= (sp.Integer(lhs) == sp.nsimplify(rhs))
    check("T == (num/den) C(M,s)^2 at grid cells (exact rationals)", ok)

    print("== [P] positivity structure ==")
    num0, den0 = forms[0]
    num1, den1 = forms[1]
    num2, den2 = forms[2]
    # den < 0 on 0 <= u <= D-10 (the domain the proof actually uses):
    # every factor is linear and (a) (u+D+c), c > 0 (positive there),
    # (b) u-D+c0 with c0 < 10, so its zero u = D-c0 lies strictly
    # above the domain -- negative there when the multiplicity is odd,
    # strictly positive when it is even (this certifies the squared
    # factors as nonvanishing, not merely nonnegative).
    for Q, den in ((0, den0), (1, den1), (2, den2)):
        const, facs = sp.factor_list(den)
        negodd = 0
        okd = const.is_number and const > 0
        for f, mult in facs:
            pf = sp.Poly(f, uv, Dv)
            if pf.total_degree() != 1:
                okd = False
                continue
            au, ad, c0_ = pf.nth(1, 0), pf.nth(0, 1), pf.nth(0, 0)
            if au == 1 and ad == 1 and c0_ > 0:
                continue                     # (u+D+c) > 0
            if au == 1 and ad == -1 and c0_ < 10:
                if mult % 2:
                    negodd += 1              # (u-D+c0) < 0 on u <= D-10
                continue
            okd = False
        check(f"Q={Q}: den < 0 and squares nonvanishing on u <= D-10 "
              f"(all factors classified)", okd and negodd % 2 == 1)
    # Q=2: -num2 = D(D-1) S2 with S2 = sum c_j u^j
    S2 = sp.expand(sp.cancel(-num2/(Dv*(Dv-1))))
    check("-num2 == D(D-1) S2 exactly (polynomial division)",
          sp.expand(-num2 - Dv*(Dv-1)*S2) == 0)
    pe = sp.Poly(S2, uv)
    cc = [sp.expand(pe.nth(j)) for j in range(6)]
    check("Q=2: S2 has degree 5", pe.degree() == 5)
    check("c0 == 3D(D+2)", sp.expand(cc[0] - 3*Dv*(Dv+2)) == 0)
    check("c1 == (D+2)(3D-4)",
          sp.expand(cc[1] - (Dv+2)*(3*Dv-4)) == 0)
    check("[i]  13 c0 + D c2 == D(33D+70)",
          sp.expand(13*cc[0] + Dv*cc[2] - Dv*(33*Dv+70)) == 0)
    check("[ii] 13 c1 + D c3 == 37D^2+30D-104",
          sp.expand(13*cc[1] + Dv*cc[3] - (37*Dv**2+30*Dv-104)) == 0)
    check("c4 == 5 and c5 == 1", cc[4] == 5 and cc[5] == 1)
    check("c2 == -2(3D+4), c3 == -2(D-2)",
          sp.expand(cc[2] + 2*(3*Dv+4)) == 0
          and sp.expand(cc[3] + 2*(Dv-2)) == 0)

    print("== [G] strip >= gap (Q = 2) ==")
    # every quantified inequality is certified on its full ray by
    # coefficient nonnegativity after the ray substitution D = D0 + r,
    # not by a single spot value:
    rv = sp.Symbol('r', nonnegative=True)
    def coeff_nonneg_on_ray(expr, D0, strict):
        pe = sp.Poly(sp.expand(expr.subs(Dv, D0 + rv)), rv)
        cs = pe.all_coeffs()
        if not all(c >= 0 for c in cs):
            return False
        return (cs[-1] > 0) if strict else True
    check("13(D+3)^2 - D(13D-9) == 87D + 117",
          sp.expand(13*(Dv+3)**2 - Dv*(13*Dv-9) - (87*Dv+117)) == 0)
    check("13(13D-9) - (87D+117) == 82D-234 >= 0 for all D >= 3",
          sp.expand(13*(13*Dv-9) - (87*Dv+117) - (82*Dv-234)) == 0
          and coeff_nonneg_on_ray(82*Dv - 234, 3, strict=False))
    check("h - sqrt(E) == 13D-9 > 0 for all D >= 1",
          sp.expand((14*Dv-6) - (Dv+3) - (13*Dv-9)) == 0
          and coeff_nonneg_on_ray(13*Dv - 9, 1, strict=True))
    check("h - 2 sqrt(E) == 12D-12 >= 0 for all D >= 1 "
          "(rationalization hypothesis)",
          sp.expand((14*Dv-6) - 2*(Dv+3) - (12*Dv-12)) == 0
          and coeff_nonneg_on_ray(12*Dv - 12, 1, strict=False))
    check("37D^2+30D-104 > 0 for all D >= 2",
          coeff_nonneg_on_ray(37*Dv**2 + 30*Dv - 104, 2, strict=True))
    # edge coverage: v = D-u < 10, i.e. k = (D-u)/2 <= 4, is
    # flow-covered for D >= 24: certify all twelve combinations
    # (D-2Q)^2 - 4k(D+1-k) >= 0, Q <= 2, 1 <= k <= 4, on the full ray:
    edge_ok = all(
        coeff_nonneg_on_ray((Dv-2*Q)**2 - 4*k*(Dv+1-k), 24,
                            strict=False)
        for Q in (0, 1, 2) for k in (1, 2, 3, 4))
    check("edge flow: (D-2Q)^2 >= 4k(D+1-k) for all D >= 24, "
          "Q <= 2, k <= 4 (12 ray certificates)", edge_ok)

    print("== [E] E2E grid Q <= 2, D <= 140 ==")
    ok = True; mech = {'id': 0, 'flow': 0, 'direct': 0}
    direct_maxD = -1
    for Q in (0, 1, 2):
        for M in range(Q, 141-Q):
            D = M + Q
            p = pcoef(M, Q)
            for s in range((D+1)//2, D+1):
                u = 2*s-D
                T = Tval(p, D, Q, s)
                if T < 0:
                    ok = False
                    print(f"    T < 0 at Q={Q} M={M} s={s}")
                x = M-Q
                if u <= D-10:
                    mech['id'] += 1
                elif (u+1)**2 >= (D+1)**2 - x*x:
                    mech['flow'] += 1
                else:
                    mech['direct'] += 1
                    direct_maxD = max(direct_maxD, D)
    check(f"all T >= 0; mechanisms {mech}", ok)
    check(f"direct-only cells all have D < 24 (scan-covered); "
          f"max D = {direct_maxD}", direct_maxD < 24)

    print("== SMALL ARGUMENT CASES:",
          "ALL CHECKS PASS ==" if OK else "FAILURES ==")
    raise SystemExit(0 if OK else 1)


if __name__ == '__main__':
    main()
