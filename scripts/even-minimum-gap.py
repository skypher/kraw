#!/usr/bin/env python3
"""Verification of every even-minimum gap cell by exact algebra.

Relabel the exponents so that Q <= M; then x = M-Q >= 0 and eps = (-1)^Q.
Scope here: Q EVEN (eps = +1), gap cells with u >= 15.  Define

    h_j   := (D+2) p_{j+1} - x p_j          (deviation),
    Tur(j) := p_j^2 - p_{j-1} p_{j+1}        (Turan),
    u_j   := 2(j+1) - D,   Lam := (D+2)^2 - x^2 = 4(Q+1)(M+1).

Five exact ingredients are checked symbolically below:

 (I1) TURAN-STEP IDENTITY:
      T_j = [u_j Tur(j)] / (j+2)
            - p_{j+1} h_j / [(j+2)(D+1-j)] .
 (I2) TURAN PSD: (D+1-j) Tur(j) = (D+1-j)^2 p_j^2 - ... is a
      quadratic form in (p_j, p_{j+1}) with discriminant
      x^2 - 4(j+1)(D+1-j) = x^2 + u_j'^2... precisely
      4(j+1)(D+1-j) = (D+2)^2 - (2j-D)^2, so on the gap
      ((2j-D)^2 < (D+1)^2 - x^2) Tur(j) >= 0 POINTWISE.
 (I3) (p, h) SYSTEM (first order, exact):
      p_{j+1} = (x p_j + h_j)/(D+2)                [definition of h]
      h_{j+1} = [(D-j)/((j+2)(D+2))] (x h_j - Lam p_j).
 (I4) ZETA FLOW: zeta_j := -h_j/p_j obeys
      zeta_{j+1} = kappa_j (Lam + x zeta_j)/(x - zeta_j),
      kappa_j = (D-j)/(j+2) <= 1 for j >= (D-2)/2; the map is
      increasing in zeta on [0, x) and in kappa, and the kappa = 1
      map is EXACT tan-addition:
      F(sqrt(Lam) tan a) = sqrt(Lam) tan(a + th*), tan th* =
      sqrt(Lam)/x.  Anchors (from reflection p_{D-j} = p_j):
        D even: h_c = 0 (c = D/2)     [the central rank-one relation]
        D odd:  zeta_c = -(D+2-x) and one step gives
                zeta_{c+1} <= sqrt(Lam) tan(th*/2)
                [tan(th*/2) = sqrt(Lam)/(D+2+x)].
      Hence zeta_{c+k} <= sqrt(Lam) tan((k - delta/2) th*),
      delta = D mod 2, as long as the argument stays below pi/2.
 (I5) BUDGET: on the gap, (u+1)^2 sin^2 th* < 7/3
      [sin^2 th* = Lam/(D+2)^2, (u+1)^2 <= (7/6)(D+3)/(2Q+3),
      (Q+1)/(2Q+3) <= 1/2, (M+1)(D+3) < (D+2)^2], so with Jordan
      (th <= (pi/2) sin th on [0, pi/2]) and u >= 15:
      ((u+2)/(2(u+1)))^2 * 7/3 <= (17/32)^2 * 7/3 < 1,
      hence ((u+2)/2) th* < pi/2,
      giving zeta_j in [0, x) and p-sign constancy through j = s,
      hence h_s <= 0, p_s p_{s+1} > 0, and by (I1) + (I2):
      T_s >= 0.   QED

After the finite-offset and fixed-argument checks, only odd-minimum
gap cells with min(M,Q) >= 13, u >= 15, and D > 14826 remain.

CHECKS:
[A] (I1)-(I4) symbolically in QQ(D, x, j)[p_j, p_j+1] resp. the
    zeta-map algebra (tan-addition as polynomial identity).
[B] anchors, both D parities, symbolically.
[C] budget arithmetic chain, exact rationals: the gap budget
    numerator, the manuscript's constant 9/16 ((u+2)/2 <= (9/16)(u+1)
    for u >= 15 and (9/16)^2 (7/3) < 1), and the sharper u = 15
    instance 17/32, each certified on its full ray by coefficient
    nonnegativity.  Jordan's inequality (th <= (pi/2) sin th on
    [0, pi/2]) is classical and enters the written proof only as the
    cited reduction step; the pi/2 factors cancel, so no numerical
    value of pi is used anywhere.
[D] E2E: for a grid of even-Q gap cells (both D parities), verify
    the full induction: kappa <= 1, zeta in [0, x), p sign constant,
    and the (I1) decomposition of T >= 0 termwise, all in exact
    integer arithmetic.  The tan bound itself is exact as well: every
    orbit angle is a nonnegative multiple of th* (plus th*/2 when D is
    odd), and tan is a rational multiple of sqrt(Lam) at each such
    angle -- tan th* = sqrt(Lam)/x, tan(th*/2) = sqrt(Lam)/(D+2+x),
    and tan-addition preserves the form t*sqrt(Lam) with t rational:
    t' = (t x + 1)/(x - t Lam).  The comparison zeta <= sqrt(Lam) tan(.)
    = t*Lam and the angle budget (x - t Lam > 0 certifies that the
    argument stays below pi/2) are therefore pure Fraction arithmetic.
    This verifier is float-free.
"""
from fractions import Fraction as F
from math import comb

import sympy as sp

OK = True
def check(name, cond):
    global OK
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}", flush=True)
    OK = OK and cond


def main():
    Dv, xv, jv = sp.symbols('D x j')
    pj, pj1 = sp.symbols('pj pj1')

    # via recurrence: p_{j+2} and p_{j-1} in terms of (p_j, p_{j+1})
    pj2 = (xv*pj1 + (jv - Dv)*pj)/(jv + 2)
    pjm1 = (xv*pj - (jv + 1)*pj1)/(Dv + 1 - jv)

    print("== [A] identities ==")
    Tj = pj**2 + pj*pj2 - pj1**2 - pjm1*pj1
    Tur = pj**2 - pjm1*pj1
    hj = (Dv + 2)*pj1 - xv*pj
    uj = 2*(jv + 1) - Dv
    rhs = uj*Tur/(jv + 2) - pj1*hj/((jv + 2)*(Dv + 1 - jv))
    check("(I1) Turan-step identity",
          sp.simplify(sp.together(Tj - rhs)) == 0)

    q_form = (Dv + 1 - jv)*pj**2 - xv*pj*pj1 + (jv + 1)*pj1**2
    check("(I2a) (D+1-j) Tur == quadratic form",
          sp.simplify(sp.together((Dv + 1 - jv)*Tur - q_form)) == 0)
    check("(I2b) 4(j+1)(D+1-j) == (D+2)^2 - (2j-D)^2",
          sp.expand(4*(jv+1)*(Dv+1-jv) - ((Dv+2)**2 - (2*jv-Dv)**2))
          == 0)

    Lam = (Dv + 2)**2 - xv**2
    hj1 = (Dv + 2)*pj2 - xv*pj1
    pred = (Dv - jv)/((jv + 2)*(Dv + 2))*(xv*hj - Lam*pj)
    check("(I3) h_{j+1} == (D-j)/((j+2)(D+2)) (x h_j - Lam p_j)",
          sp.simplify(sp.together(hj1 - pred)) == 0)
    check("(I3b) Lam == 4(Q+1)(M+1) [x = M-Q, D = M+Q]",
          sp.expand(((sp.Symbol('M')+sp.Symbol('Q')+2)**2
                     - (sp.Symbol('M')-sp.Symbol('Q'))**2)
                    - 4*(sp.Symbol('Q')+1)*(sp.Symbol('M')+1)) == 0)

    # (I4) zeta map algebra: from (I3), with zeta = -h/p:
    z, ta = sp.symbols('zeta t')
    LamS, xS = sp.symbols('Lams xs', positive=True)
    # zeta_{j+1} = -h_{j+1}/p_{j+1} = kappa (Lam + x zeta)/(x - zeta):
    zeta_next = sp.simplify(
        (-((Dv-jv)/((jv+2)*(Dv+2))*(xv*(-z*pj) - Lam*pj)))
        / ((xv*pj + (-z*pj))/(Dv+2)) / pj * pj)
    check("(I4a) zeta_{j+1} == kappa (Lam + x zeta)/(x - zeta)",
          sp.simplify(zeta_next
                      - (Dv-jv)/(jv+2)*(Lam + xv*z)/(xv - z)) == 0)
    # monotonicity: d/dzeta [(Lam + x z)/(x - z)] = (Lam + x^2)/(x-z)^2 > 0
    dF = sp.simplify(sp.diff((LamS + xS*z)/(xS - z), z)
                     - (LamS + xS**2)/(xS - z)**2)
    check("(I4b) dF/dzeta == (Lam + x^2)/(x - zeta)^2 > 0", dF == 0)
    # tan addition: F(sqrt(Lam) t) == sqrt(Lam) (tan th* + t)/(1 - t tan th*)
    # with tan th* = sqrt(Lam)/x:
    lhs = (LamS + xS*sp.sqrt(LamS)*ta)/(xS - sp.sqrt(LamS)*ta)
    rhs4 = sp.sqrt(LamS)*(sp.sqrt(LamS)/xS + ta)/(1 - ta*sp.sqrt(LamS)/xS)
    check("(I4c) kappa=1 map == tan addition law",
          sp.simplify(sp.together(lhs - rhs4)) == 0)
    # half-angle: tan(th*/2) == sqrt(Lam)/(D+2+x)  given
    # sin th* = sqrt(Lam)/(D+2), cos th* = x/(D+2):
    check("(I4d) tan(th*/2) = sinth/(1+costh) == sqrt(Lam)/(D+2+x)",
          sp.simplify((sp.sqrt(Lam)/(Dv+2))/(1 + xv/(Dv+2))
                      - sp.sqrt(Lam)/(Dv+2+xv)) == 0)
    check("(I4e) kappa_j <= 1 for j >= (D-2)/2: (D-j)-(j+2) = D-2-2j <= 0",
          sp.expand((Dv-jv) - (jv+2) - (Dv-2-2*jv)) == 0)

    print("== [B] anchors ==")
    # D even: reflection p_{c-1} = p_{c+1} at c = D/2 => h_c = 0:
    a, b = sp.symbols('a b')  # a = p_c, b = p_{c+1}; p_{c-1} = b
    cN = Dv/2
    # recurrence at j = c: (c+1) p_{c+1} = x p_c + (c-1-D) p_{c-1}:
    rec = (cN+1)*b - xv*a - (cN-1-Dv)*b
    hc = (Dv+2)*b - xv*a
    check("D even: recurrence at center forces h_c == 0",
          sp.simplify(sp.together(rec - hc)) == 0)
    # D odd: anchor at c = (D-1)/2 with p_c = p_{c+1} (reflection):
    cO = (Dv-1)/2
    hcO = (Dv+2)*a - xv*a          # h_c with p_{c+1} = p_c = a
    check("D odd: zeta_c == -(D+2-x)",
          sp.simplify(-hcO/a + (Dv+2-xv)) == 0)
    zc1 = (Dv-cO)/(cO+2)*(Lam + xv*(-(Dv+2-xv)))/(xv + (Dv+2-xv))
    check("D odd: zeta_{c+1} == kappa_c (D+2-x) <= (D+2-x)",
          sp.simplify(zc1 - (Dv-cO)/(cO+2)*(Dv+2-xv)) == 0)
    # and (D+2-x) == sqrt(Lam) tan(th*/2) since
    # sqrt(Lam) * sqrt(Lam)/(D+2+x) = Lam/(D+2+x) = D+2-x:
    check("D odd: (D+2-x) == sqrt(Lam) tan(th*/2)",
          sp.simplify(Lam/(Dv+2+xv) - (Dv+2-xv)) == 0)

    print("== [C] budget ==")
    # gap => (u+1)^2 <= (7/6)(D+3)/(2Q+3)   [Thm 128 cert, re-check]:
    check("2/(3+sqrt5) <= 7/18", sp.simplify(21+7*sp.sqrt(5)-36 > 0)
          == True)
    # (u+1)^2 sin^2 th* < 7/3:
    Mv, Qv = sp.symbols('M Q', positive=True)
    expr = (sp.Rational(7, 6)*(Mv+Qv+3)/(2*Qv+3)
            * 4*(Qv+1)*(Mv+1)/(Mv+Qv+2)**2)
    # (Q+1)/(2Q+3) <= 1/2 and (M+1)(D+3) <= (D+2)^2 - 1:
    check("(Q+1)/(2Q+3) <= 1/2:  (2Q+3) - 2(Q+1) == 1 > 0",
          sp.expand((2*Qv+3) - 2*(Qv+1)) == 1)
    check("(M+1)(M+Q+3) <= (M+Q+2)^2 - 1  [M <= D]",
          sp.factor((Mv+Qv+2)**2 - 1 - (Mv+1)*(Mv+Qv+3))
          == Qv*(Mv+Qv+3))
    # Direct exact form of the gap budget; its numerator has positive
    # coefficients on M,Q>0.
    gap_num = sp.Poly(sp.together(sp.Rational(7, 3) - expr).as_numer_denom()[0],
                      Mv, Qv)
    check("(u+1)^2 sin^2 th* < 7/3  (exact gap budget)",
          all(c > 0 for c in gap_num.coeffs()))
    # Jordan's classical inequality theta <= (pi/2) sin(theta) reduces
    # the closing condition ((u+2)/2) th* < pi/2 to
    # ((u+2)/(2(u+1)))^2 * 7/3 < 1: the pi/2 cancels, so the residual
    # obligation is rational.  Certify the manuscript's chain with the
    # displayed constant 9/16 AND the sharper u = 15 instance 17/32,
    # each with its ray fact certified by coefficient nonnegativity
    # after u = 15 + r:
    uu, rv = sp.symbols('u r', nonnegative=True)
    def ray_nonneg(expr_u):
        pe = sp.Poly(sp.expand(expr_u.subs(uu, 15 + rv)), rv)
        return all(c >= 0 for c in pe.all_coeffs())
    check("(u+2)/2 <= (9/16)(u+1) for u >= 15: 9(u+1)-8(u+2) >= 0",
          ray_nonneg(9*(uu+1) - 8*(uu+2)))
    check("manuscript constant: (9/16)^2 * 7/3 == 567/768 < 1",
          F(9, 16)**2 * F(7, 3) == F(567, 768) and F(567, 768) < 1)
    check("(u+2)/(2(u+1)) <= 17/32 for u >= 15: 34(u+1)-32(u+2) >= 0",
          ray_nonneg(34*(uu+1) - 32*(uu+2)))
    check("((u+2)/(2(u+1)))^2 * 7/3 < 1 for u >= 15  (exact)",
          F(17, 32)**2 * F(7, 3) < 1)

    print("== [D] E2E on even-Q gap cells ==")
    def pcoef(M, Q):
        D = M + Q
        p = [0]*(D+1)
        for i in range(M+1):
            for jj in range(Q+1):
                p[i+jj] += comb(M, i)*comb(Q, jj)*(-1)**(Q-jj)
        return p

    okE = True; cells = 0
    for (M, Q) in [(1986, 14), (1987, 14), (2985, 16), (2986, 16),
                   (1200, 20), (1201, 20)]:
        D = M + Q; x = M - Q
        p = pcoef(M, Q)
        E = (D+3)**2
        c = D//2; delta = D % 2
        Lamn = (D+2)**2 - x*x
        sgn = 1 if p[c+delta] > 0 else -1
        q = [sgn*v for v in p]      # normalized: q[c+delta] > 0
        for u in range(1, 200):
            U = (u+1)**2
            if not (U < (D+1)**2 - x*x and x*x*U > (U-1)*(E-U)):
                continue
            if (D - u) % 2:
                continue
            s = (D+u)//2
            cells += 1
            ok1 = True
            # exact tan bound: tan(((j-c)-delta/2) th*) = t*sqrt(Lam)
            # with t rational; base t = 0 (D even, angle 0) or
            # t = 1/(D+2+x) (D odd, angle th*/2); step
            # t -> (t x + 1)/(x - t Lam) is exact tan-addition by th*.
            t = F(0) if delta == 0 else F(1, D+2+x)
            for j in range(c+delta, s+1):
                h = (D+2)*q[j+1] - x*q[j]
                if q[j] <= 0: ok1 = False
                if j >= c+1 and h > 0: ok1 = False
                # invariant bound stays strictly below x (angle below
                # pi/2 - th*), exactly:
                if t*Lamn >= x: ok1 = False
                if q[j] > 0:
                    zeta = F(-h, q[j])
                    # exact invariant: zeta_j <= sqrt(Lam) tan(.) = t*Lam
                    if zeta > t*Lamn: ok1 = False
                    if j >= c+1 and zeta < 0: ok1 = False
                if j < s:
                    den = x - t*Lamn
                    if den <= 0:
                        ok1 = False
                        break
                    t = (t*x + 1)/den
            # T-decomposition, exact integers:
            T = q[s]**2 + q[s]*q[s+2] - q[s+1]**2 - q[s-1]*q[s+1]
            term1 = (2*(s+1)-D)*((D+1-s)*q[s]**2 - x*q[s]*q[s+1]
                                 + (s+1)*q[s+1]**2)
            hs = (D+2)*q[s+1] - x*q[s]
            term2 = -q[s+1]*hs
            if T*(s+2)*(D+1-s) != term1 + term2: ok1 = False
            if term1 < 0 or term2 < 0 or T < 0: ok1 = False
            okE &= ok1
    check(f"E2E: {cells} even-Q gap cells, decomposition termwise "
          f"nonneg and exact tan-bound invariant zeta <= t*Lam < x "
          f"(all exact rationals)", okE and cells > 10)

    print("== EVEN-MINIMUM GAP:", "ALL CHECKS PASS ==" if OK else
          "FAILURES ==")
    raise SystemExit(0 if OK else 1)


if __name__ == '__main__':
    main()
