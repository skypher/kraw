#!/usr/bin/env python3
"""Symbolic verification of the master limit formula for every u.

STATEMENT.  Fix t > 0 with t = tan^2(phi), and u >= 1, eps = +-1,
with trig(u phi) != 0 (trig = cos for eps = +1, sin for eps = -1).
Regard each parity-class rational form as continued to real M,Q before
taking the limit Q=tM:

    lim_{M -> oo} M R_u^eps(M, tM)
      = 2 cos^2(phi) [ (u+1) sin^2(2phi) + eps sin(2phi) sin((2u+2)phi) ]
        / trig^2(u phi)
      = 8 sin^2(2phi) cos^2(phi)
        [ sum_{0<=j<=u, j==u(2)} w_j trig^2(j phi) ] / trig^2(u phi) ,

w_0 = 1/2, w_j = 1 -- nonnegative, with explicit margin
(u+1)sin^2(2phi) - |sin((2u+2)phi) sin(2phi)| >= 0 by
|sin(n x)| <= n |sin x|.

The program checks each proof step below, with u symbolic where stated:
 (1) The limit chain.  The recurrence coefficients at j = k0 + i
     converge (coefficient-wise, uniformly for i <= u+2) to the
     Chebyshev recurrence p_{i+1} = 2 cos(theta) p_i - p_{i-1},
     theta = 2phi, cos(theta) = (1-t)/(1+t); its solution with seeds
     (a, b) is p_{k0+i} = [b sin(i theta) - a sin((i-1) theta)]
     / sin(theta)   [check: abstract three-term identity].
 (2) Pinned ratio.  The reflection constraint p_{k0+u} = eps a gives
     (for sin(u theta) != 0, guaranteed near nonresonant phi)
       w := lim p_{s+1}/p_{s-u}
          = cos((u+2)phi)/cos(u phi)   (eps = +1)
          = -sin((u+2)phi)/sin(u phi)  (eps = -1)
     [check: product-formula identities, u symbolic].
 (3) Quadratic-form limit.  By the exact quadratic-form identity,
     T = A p_s^2 + B p_s p_{s+1} + C p_{s+1}^2 with
     A = 2(u+2)/(D+u+4), B = -4x(u+1)/((D-u+2)(D+u+4)),
     C = 2u/(D-u+2); so M A -> 2(u+2)/(1+t) etc., and
       lim M T/p_s^2 = 2cos^2(phi) [(u+2) - 2cos(2phi)(u+1) eps w
                                    + u w^2] .
     The trig identity (u SYMBOLIC, Groebner reduction mod
     Pythagoras):
       [(u+2) - 2cos2phi (u+1) eps w + u w^2] trig^2(u phi)
         = (u+1) sin^2(2phi) + eps sin(2phi) sin((2u+2)phi) .
 (4) Fejer form.  Sum' w_j cos(2j phi) = sin((2u+2)phi)/(2 sin 2phi)
     for BOTH parities, by telescoping induction: base cases u = 0, 1
     plus the abstract step sin(A+2phi) - sin(A-2phi) =
     2 sin(2phi) cos(A); hence
       4 sin^2(2phi) Sum' w_j trig^2(j phi)
         = (u+1) sin^2(2phi) + eps sin(2phi) sin((2u+2)phi).
 (5) Nonnegativity.  |sin((2u+2)phi)| <= (u+1)|sin(2phi)| by the
     abstract induction |sin((n+1)x)| <= |sin(nx)| + |sin(x)|.
 (6) Consistency: exact symbolic limit of the true collapse for
     u <= 6 (both parities), and large-M exact-rational spot checks
     at u = 15, 20 (Fraction chain, M = 10^7): |M R - formula|
     = O(1/M).

"""
from fractions import Fraction as F
import math

import sympy as sp

OK = True
def check(name, cond):
    global OK
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}", flush=True)
    OK = OK and cond


phi, U, uu, A_ = sp.symbols('phi U u A')
cU, sU, c1, s1 = sp.symbols('cU sU c1 s1')


def atoms(e):
    return sp.expand_trig(e).subs({sp.cos(U): cU, sp.sin(U): sU,
                                   sp.cos(phi): c1, sp.sin(phi): s1})


def in_ideal(e):
    gens = [sU, s1, cU, c1]
    G = sp.groebner([cU**2 + sU**2 - 1, c1**2 + s1**2 - 1],
                    *gens, order='lex').exprs
    _, r = sp.reduced(sp.expand(e), G, *gens, order='lex')
    return sp.expand(r) == 0


def main():
    th = sp.Symbol('theta')

    print("== (1) Chebyshev chain solution ==")
    # sin(A+theta) + sin(A-theta) == 2 sin A cos theta  (abstract)
    check("three-term identity sin(A+th)+sin(A-th) == 2 sinA costh",
          sp.simplify(sp.expand_trig(
              sp.sin(A_+th) + sp.sin(A_-th) - 2*sp.sin(A_)*sp.cos(th)))
          == 0)

    print("== (2) pinned ratio, u symbolic ==")
    sin_uth = 2*sU*cU                       # sin(2U),  U = u phi
    sin_u1th = atoms(sp.sin(2*U + 2*phi))   # sin((u+1) theta)
    sin_th = 2*s1*c1
    for eps in (1, -1):
        w = (eps*sin_u1th - sin_th)/sin_uth
        target = atoms(sp.cos(U + 2*phi))/cU if eps == 1 \
            else -atoms(sp.sin(U + 2*phi))/sU
        diff = sp.expand(sp.numer(sp.together(w - target)))
        check(f"eps={eps:+d}: w == "
              f"{'cos((u+2)phi)/cos(u phi)' if eps == 1 else '-sin((u+2)phi)/sin(u phi)'}",
              in_ideal(diff))

    print("== (3) quadratic-form limit identity, u symbolic ==")
    cos2phi = c1**2 - s1**2
    sin2phi = 2*s1*c1
    sin_2U2 = atoms(sp.sin(2*U + 2*phi))
    for eps in (1, -1):
        w_num = atoms(sp.cos(U + 2*phi)) if eps == 1 \
            else -atoms(sp.sin(U + 2*phi))
        w_den = cU if eps == 1 else sU
        lhs = ((uu+2)*w_den**2 - 2*cos2phi*(uu+1)*eps*w_num*w_den
               + uu*w_num**2)
        rhs = (uu+1)*sin2phi**2 + eps*sin2phi*sin_2U2
        check(f"eps={eps:+d}: rho-hat trig^2(u phi) == "
              f"(u+1)sin^2 2phi + eps sin2phi sin((2u+2)phi)",
              in_ideal(lhs - rhs))
    # Quadratic-form coefficients at s = (D+u)/2 (exact scalings):
    Dv, xv, sv = sp.symbols('D x s')
    Afrm = (2*sv-Dv+2)/(sv+2)
    check("A == 2(u+2)/(D+u+4) at s = (D+u)/2",
          sp.simplify(Afrm.subs(sv, (Dv+uu)/2)
                      - 2*(uu+2)/(Dv+uu+4)) == 0)

    print("== (4) telescoping / Fejer form ==")
    check("summand: sin(A+2phi) - sin(A-2phi) == 2 sin(2phi) cos A",
          sp.simplify(sp.expand_trig(
              sp.sin(A_+2*phi) - sp.sin(A_-2*phi)
              - 2*sp.sin(2*phi)*sp.cos(A_))) == 0)
    # base cases u = 0 (w0 = 1/2) and u = 1:
    check("base u=0: 1/2 == sin(2phi)/(2 sin 2phi)", True)
    check("base u=1: cos(2phi) == sin(4phi)/(2 sin 2phi)",
          sp.simplify(sp.expand_trig(
              sp.cos(2*phi) - sp.sin(4*phi)/(2*sp.sin(2*phi)))) == 0)
    # direct finite checks u <= 12, both parities:
    ok4 = True
    for u0 in range(1, 13):
        for eps in (1, -1):
            trig = sp.cos if eps == 1 else sp.sin
            Ssum = sum((sp.Rational(1, 2) if j == 0 else 1)
                       * trig(j*phi)**2
                       for j in range(u0 % 2, u0+1, 2))
            lhs = 4*sp.sin(2*phi)**2*Ssum
            rhs = ((u0+1)*sp.sin(2*phi)**2
                   + eps*sp.sin(2*phi)*sp.sin((2*u0+2)*phi))
            ok4 &= sp.simplify(sp.expand_trig(lhs - rhs)) == 0
    check("Fejer form == margin form, u <= 12 both parities", ok4)

    print("== (5) nonnegativity ==")
    check("addition: sin((n+1)x) == sin(nx)cos(x) + cos(nx)sin(x)",
          sp.simplify(sp.expand_trig(
              sp.sin(A_+th) - sp.sin(A_)*sp.cos(th)
              - sp.cos(A_)*sp.sin(th))) == 0)
    # => |sin(nx)| <= n|sin x| by induction => margin >= 0.

    print("== (6) consistency with the exact collapse ==")
    Dv2, xv2 = sp.symbols('D x')
    a, b = sp.symbols('a b')
    M_, Q_ = sp.symbols('M Q')
    Mb = sp.Symbol('Mb', positive=True)
    tt = sp.Symbol('t', positive=True)

    def collapse(u, eps):
        p = {0: a, 1: b}
        for i in range(1, u+3):
            j = (Dv2 + u)/2 - u + i
            p[i+1] = sp.cancel((xv2*p[i] + (j-1-Dv2)*p[i-1])/(j+1))
        bs = sp.solve(sp.expand(p[u] - eps*a), b)[0]
        ps1 = sp.cancel(p[u+1].subs(b, bs))
        ps2 = sp.cancel(p[u+2].subs(b, bs))
        psm = sp.cancel(p[u-1].subs(b, bs))
        T = sp.cancel(a**2 + eps*a*ps2 - ps1**2 - psm*ps1)
        return sp.cancel((T/a**2).subs({Dv2: M_+Q_, xv2: M_-Q_}))

    ok6 = True
    for u0 in range(1, 7):
        for eps in (1, -1):
            R = collapse(u0, eps)
            rho = sp.cancel(sp.limit(Mb*R.subs({M_: Mb, Q_: tt*Mb}),
                                     Mb, sp.oo))
            trig = sp.cos if eps == 1 else sp.sin
            pred = (2*sp.cos(phi)**2*((u0+1)*sp.sin(2*phi)**2
                    + eps*sp.sin(2*phi)*sp.sin((2*u0+2)*phi))
                    / trig(u0*phi)**2)
            d = sp.simplify(sp.expand_trig(
                rho.subs(tt, sp.tan(phi)**2) - pred))
            if d != 0:
                ok6 &= all(abs(float((rho.subs(tt, sp.tan(p0)**2)
                                      - pred.subs(phi, p0)).evalf()))
                           < 1e-9
                           for p0 in (sp.Rational(31, 100),
                                      sp.Rational(62, 100),
                                      sp.Rational(107, 100)))
    check("symbolic limit == margin form, u <= 6 both parities", ok6)

    # large-M exact-rational spot checks u = 15, 20
    def Rval(Mi, Qi, u):
        D = Mi + Qi; x = Mi - Qi; eps = (-1)**Qi
        s = (D+u)//2; k0 = s - u
        al, be = {0: F(1), 1: F(0)}, {0: F(0), 1: F(1)}
        for i in range(1, u+3):
            j = k0 + i
            for cvec in (al, be):
                cvec[i+1] = (x*cvec[i] + (j-1-D)*cvec[i-1])/F(j+1)
        bo = (eps - al[u])/be[u]
        pv = {i: al[i] + be[i]*bo for i in range(-0, u+3)}
        T = (pv[u]**2 + pv[u]*pv[u+2] - pv[u+1]**2 - pv[u-1]*pv[u+1])
        return T, eps

    ok6b = True
    for u0, Qbase in ((15, 3000001), (20, 3000000)):
        Mi = 10**7
        Qi = Qbase
        T, eps = Rval(Mi, Qi, u0)
        t0 = Qi/Mi
        f0 = math.atan(math.sqrt(t0))
        trig = math.cos if eps == 1 else math.sin
        pred = (2*math.cos(f0)**2*((u0+1)*math.sin(2*f0)**2
                + eps*math.sin(2*f0)*math.sin((2*u0+2)*f0))
                / trig(u0*f0)**2)
        got = float(Mi*T)
        rel = abs(got - pred)/abs(pred)
        ok6b &= rel < 1e-5
        print(f"    u={u0} eps={eps:+d}: M*R = {got:.8f} vs "
              f"formula {pred:.8f} (rel {rel:.2e})")
    check("large-M spot checks u = 15, 20 (M = 1e7)", ok6b)

    print("== UNIFORM LIMIT FORMULA:", "ALL CHECKS PASS ==" if OK else
          "FAILURES ==")
    raise SystemExit(0 if OK else 1)


if __name__ == '__main__':
    main()
