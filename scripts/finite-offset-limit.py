#!/usr/bin/env python3
"""Finite-offset checks of the master limit formula through u=10.

Here T_s is the Turan step of p_s = [w^s](1+w)^M(1-w)^Q, and
reflection gives T_s = R_u(M,Q)
p_{s-u}^2 at s = (D+u)/2, eps = (-1)^Q.  In the joint central limit
M -> oo with t = Q/M fixed, write t = tan^2(phi):

    lim_{M->oo}  M * R_u^eps(M, tM)
        = 8 sin^2(2phi) cos^2(phi) *
          [ sum_{0 <= j <= u, j = u mod 2} w_j trig^2(j phi) ]
          / trig^2(u phi) ,

with trig = cos for eps = +1, trig = sin for eps = -1, and weights
w_0 = 1/2, w_j = 1 (j >= 1).  A Fejer-type POSITIVE kernel: the gap
margin is manifestly positive at leading order 1/M, UNIFORMLY in u.
(The denominators' zero loci trig(u phi) = 0 are exactly the
Chebyshev resonances observed in the collapse gcds, e.g. beta_8's top
form M^4 - 28M^3Q + 70M^2Q^2 - 28MQ^3 + Q^4 = Re[(sqrt M - i sqrt
Q)^8]; there p_{s-u} -> 0 and T stays finite.)

CHECK: for u = 1..10 and both parity classes, compute R_u by the
reflection collapse (exact sympy), take the limit, and verify the
closed form SYMBOLICALLY (difference simplifies to 0; numeric
fallback at three angles guards against simplifier failure).
"""
import sympy as sp

OK = True
def check(name, cond):
    global OK
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}", flush=True)
    OK = OK and cond


Dv, xv = sp.symbols('D x')
a, b = sp.symbols('a b')
M_, Q_ = sp.symbols('M Q')


def collapse(u, eps):
    p = {0: a, 1: b}
    for i in range(1, u+3):
        j = (Dv + u)/2 - u + i
        p[i+1] = sp.cancel((xv*p[i] + (j - 1 - Dv)*p[i-1])/(j + 1))
    bs = sp.solve(sp.expand(p[u] - eps*a), b)[0]
    ps1 = sp.cancel(p[u+1].subs(b, bs))
    ps2 = sp.cancel(p[u+2].subs(b, bs))
    psm = sp.cancel(p[u-1].subs(b, bs))
    T = sp.cancel(a**2 + eps*a*ps2 - ps1**2 - psm*ps1)
    return sp.cancel((T/a**2).subs({Dv: M_+Q_, xv: M_-Q_}))


def main():
    Mb = sp.Symbol('Mb', positive=True)
    tt = sp.Symbol('t', positive=True)
    phi = sp.Symbol('phi', positive=True)
    for u in range(1, 11):
        for eps in (1, -1):
            R = collapse(u, eps)
            rho = sp.cancel(sp.limit(Mb*R.subs({M_: Mb, Q_: tt*Mb}),
                                     Mb, sp.oo))
            trig = sp.cos if eps == 1 else sp.sin
            S = sum((sp.Rational(1, 2) if j == 0 else 1)*trig(j*phi)**2
                    for j in range(u % 2, u+1, 2))
            pred = 8*sp.sin(2*phi)**2*sp.cos(phi)**2*S/trig(u*phi)**2
            diff = sp.simplify(sp.expand_trig(
                rho.subs(tt, sp.tan(phi)**2) - pred).rewrite(sp.sin))
            ok = (diff == 0)
            if not ok:
                ok = all(abs(float((rho.subs(tt, sp.tan(p0)**2)
                                    - pred.subs(phi, p0)).evalf())) < 1e-9
                         for p0 in (sp.Rational(31, 100),
                                    sp.Rational(62, 100),
                                    sp.Rational(107, 100)))
            check(f"u={u} eps={eps:+d}: master limit formula", ok)
    print("== FINITE-OFFSET LIMIT:", "ALL CHECKS PASS ==" if OK else "FAILURES ==")
    raise SystemExit(0 if OK else 1)


if __name__ == '__main__':
    main()
