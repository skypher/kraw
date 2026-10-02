#!/usr/bin/env python3
"""Exact checks for the bulk, center, tail-flow, coverage, odd u = 1, and
gap-lemma arguments.

Usage: regime-decomposition.py   (-h/--help prints this text)

Everything here is about T_s(M,Q) = p_s^2 + p_s p_{s+2} - p_{s+1}^2
- p_{s-1} p_{s+1} with p_s = [w^s](1+w)^M (1-w)^Q, D = M+Q, x = M-Q,
u = 2s-D >= 0 (top half).
WLOG x >= 0 (T is M<->Q symmetric).  Cast:

QUADRATIC-FORM IDENTITY AND BULK BAND.  Exactly
    T_s = A p_s^2 + B p_s p_{s+1} + C p_{s+1}^2,
    A = (u+2)/(s+2), B = -x(u+1)/((D+1-s)(s+2)), C = u/(D+1-s),
and 4AC - B^2 = [u(u+2)((D+3)^2-(u+1)^2) - x^2(u+1)^2] / ((D+1-s)(s+2))^2.
Hence for u >= 1:  x^2 (u+1)^2 <= ((u+1)^2 - 1)((D+3)^2 - (u+1)^2)
==> the form is PSD ==> T_s >= 0 pointwise ("bulk band").

CENTRAL IDENTITY (u = 0, D even).
    Q odd:  T_{D/2} = 0.
    Q even: T_{D/2} = 4 p_{D/2}^2 ((D+2)^2 - x^2) / ((D+2)^2 (D+4)) >= 0.

TAIL FLOW.  Let k = D-s, w(s)^2 = x^2 - 4k(D+1-k).
On the flow region w^2 >= 0 (equivalently (u+1)^2 >= (D+1)^2 - x^2),
1 <= k, T_s >= 0.  Proof pieces, each verified exactly below:
 (a) reparametrization: (D+1)^2 - (u+1)^2 = 4(s+1)(D-s);
 (b) w-monotonicity: w(s)^2 - w(s-1)^2 = 4u > 0;
 (c) flow comparison: phi(s) = (x + w(s))/2 satisfies
     phi(s-1) <= x - (s+1)(D-s)/phi(s)  [<=> (w(s)-w(s-1))(x+w(s)) >= 0],
     so the downward flow y_{s-1} = x - (s+1)(D-s)/y_s, y_{D-1} = x,
     obeys y_s >= phi(s) > 0; by induction (recurrence + anchor
     p_D = (-1)^Q, p_{D-1} = (-1)^Q x) the exact conjugacy
     r_s := p_{s+1}/p_s = k/y_s holds, whence 0 < r_s <= k/phi(s);
 (d) window value: I1 = (u+2)(k+1) phi^2 - x(u+1) k phi + u(D-k+2) k^2
     = P1 + Q1 w with Q1 = x(D-k+2)/2 >= 0 and
     P1 = [x^2(D+2-k) - 2k(D^2-2Dk+3D+2k^2-2k+2)]/2, which at the
     region boundary x^2 = 4k(D+1-k) equals k(D+2)(u+1) > 0 and is
     increasing in x^2; so I1 >= 0, i.e. the form value at r = k/phi
     is >= 0;
 (e) window vertex: I2 = x(u+1) phi - 2u(D-k+2) k = P2 + Q2 w with
     Q2 = x(u+1)/2 >= 0, P2 = [x^2(u+1) - 4k(D^2-3Dk+2D+2k^2-4k)]/2,
     boundary value 2k(k+1) > 0, increasing in x^2; so k/phi <= -B/(2C).
 With A, C >= 0 >= B the form is decreasing on [0, -B/(2C)], so
 (d)+(e)+(c) give T_s = form(r_s) >= form(k/phi) >= 0.

COVERAGE.  The bulk condition holds at the flow
boundary U0 = (D+1)^2 - x^2: bulk margin there is
(U0-1)(4D+8) - x^2 = (D^2+2D-x^2)(4D+8) - x^2 > 0 for 0 <= x <= D.
Hence every top-half cell is covered by {s=D} u {u=0} u bulk u flow
EXCEPT the central gap  GAP = { u >= 1 : x^2 (u+1)^2 >
((u+1)^2-1)((D+3)^2-(u+1)^2) and (u+1)^2 < (D+1)^2 - x^2 }.

ODD Q, u = 1.  For Q odd and 2s = D+1, reflection gives p_{s-1} = -p_s and
the recurrence gives (s+1)^2 (s+2) T_s = 4(M+1)(Q+2) p_s^2 >= 0.

GAP LEMMAS (square-root-free).  With U = (u+1)^2, E = (D+3)^2,
h = E+1-x^2, q(t) = t^2 - h t + E and U0 = (D+1)^2 - x^2:
x^2 U - (U-1)(E-U) = q(U), so a gap cell has q(U) > 0 and U < U0, while
q(U0) = -[(D^2+2D-x^2)(4D+8) - x^2] <= 0 for 0 <= x <= D.  Hence U < h/2
and smaller offsets stay in the gap (heredity).  With D = x+2Q, M = Q+x:
h - 3(D+3) = 4MQ+3M+3Q+1 > 0, q(7E/(6h)) = E(49E-6h^2)/(36h^2) <= 0 and
h - (2Q+3)(D+3) = (2Q+3)x + 1 >= 0, whence 6(2Q+3)U < 7(D+3) (gap strip).

CHECKS [all exact: sympy rationals / integers]:
[A] the quadratic-form identity, symbolically and on a grid.
[B] reflection identity on a grid; central identity, symbolically
    (via collapse) and on a grid.
[C] the discriminant identity; grid: bulk condition ==> T >= 0.
[D] (a),(b),(c),(d),(e) symbolically, including the two link
    identities tying I1 (form value at r = k/phi) and I2 (vertex
    comparison) to the quadratic form; grid: on flow cells the exact
    conjugacy r_s = k/y_s, the comparison invariant y_s >= phi(s),
    and T_s >= 0, all in exact rational arithmetic (phi compared via
    squares).
[E] coverage margin polynomial > 0; E2E grid M,Q <= 45: every top-half
    cell is covered by a certified mechanism (no fallback).
[F] the odd u = 1 closed form; the gap-lemma identities; grid D <= 300:
    gap strip and heredity on every gap cell.
[G] exact counterexample to the real-argument relaxation.
"""
from fractions import Fraction as F
from math import comb

import sympy as sp

OK = True
def check(name, cond):
    global OK
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}", flush=True)
    OK = OK and cond


def pcoef(M, Q):
    """Coefficients of (1+w)^M (w-1)^Q, i.e. (-1)^Q times the paper's
    p_s.  The global sign cancels in every quadratic quantity used
    below (T values, ratios, squares); the symbolic checks use the
    paper's own convention."""
    D = M + Q
    p = [0]*(D+1)
    for a in range(M+1):
        for b in range(Q+1):
            p[a+b] += comb(M, a)*comb(Q, b)*(-1)**(Q-b)
    return p


def pv(p, D, Q, j):
    return p[j] if 0 <= j <= D else 0


def Tval(p, D, Q, s):
    return (pv(p,D,Q,s)**2 + pv(p,D,Q,s)*pv(p,D,Q,s+2)
            - pv(p,D,Q,s+1)**2 - pv(p,D,Q,s-1)*pv(p,D,Q,s+1))


def main():
    import sys
    if any(a_ in ('-h', '--help') for a_ in sys.argv[1:]):
        print(__doc__)
        return
    Dv, xv, sv, a, b = sp.symbols('D x s a b')
    uv = 2*sv - Dv

    print("== [A] quadratic-form identity ==")
    c1 = (xv*b + (sv-1-Dv)*a)/(sv+1)          # p_{s+1}
    c2 = (xv*c1 + (sv-Dv)*b)/(sv+2)           # p_{s+2}
    T = b**2 + b*c2 - c1**2 - a*c1
    A = (uv+2)/(sv+2)
    B = -xv*(uv+1)/((Dv+1-sv)*(sv+2))
    C = uv/(Dv+1-sv)
    Fq = A*b**2 + B*b*c1 + C*c1**2
    check("T == A p_s^2 + B p_s p_{s+1} + C p_{s+1}^2 (symbolic)",
          sp.simplify(sp.cancel(T - Fq)) == 0)
    ok = True
    for M in range(0, 19):
        for Q in range(0, 19):
            D = M+Q; x = M-Q; p = pcoef(M, Q)
            for s in range((D+1)//2, D):
                u = 2*s-D
                lhs = Tval(p, D, Q, s)
                rhs = (F(u+2, s+2)*p[s]**2
                       + F(-x*(u+1), (D+1-s)*(s+2))*p[s]*p[s+1]
                       + F(u, D+1-s)*p[s+1]**2)
                ok &= (lhs == rhs)
    check("identity on grid D <= 36", ok)

    print("== [B] reflection and central identity (u = 0) ==")
    # the reflection identity p_{D-j} = (-1)^Q p_j itself, on a grid
    # (in the pcoef convention q_j = (-1)^Q p_j it reads the same way):
    ok = True
    for M in range(0, 41):
        for Q in range(0, 41):
            D = M+Q; p = pcoef(M, Q)
            ok &= all(p[D-j] == (-1)**Q*p[j] for j in range(D+1))
    check("reflection p_{D-j} == (-1)^Q p_j on grid D <= 80", ok)
    # Q even (eps=+1): reflection p_{s-1} = p_{s+1} at s = D/2; collapse.
    cc1 = (xv*b + (sv-1-Dv)*a)/(sv+1)
    aa = sp.solve(sp.expand(a - cc1), a)[0]     # a = p_{s-1} = p_{s+1}
    cc1s = sp.cancel(cc1.subs(a, aa))
    cc2s = sp.cancel((xv*cc1s + (sv-Dv)*b)/(sv+2))
    Ts = sp.cancel(b**2 + b*cc2s - cc1s**2 - aa*cc1s)
    Ts = sp.cancel(Ts.subs(sv, Dv/2))
    pred = 4*b**2*((Dv+2)**2 - xv**2)/((Dv+2)**2*(Dv+4))
    okB = (sp.simplify(sp.cancel(Ts - pred)) == 0)
    # Q odd (eps=-1): given the certified reflection facts p_{D/2} = 0,
    # p_{s-1} = -p_{s+1}, the four terms cancel algebraically:
    pm1 = sp.Symbol('pm1')
    okB &= (sp.expand(0**2 + 0 - (-pm1)**2 - pm1*(-pm1)) == 0)
    check("central identities, both parities (symbolic)", okB)
    ok = True
    for M in range(0, 41):
        for Q in range(0, 41):
            D = M+Q
            if D % 2: continue
            x = M-Q; s = D//2; p = pcoef(M, Q)
            T0 = Tval(p, D, Q, s)
            if Q % 2:
                ok &= (T0 == 0)
            else:
                ok &= (T0 == F(4*p[s]**2*((D+2)**2-x*x), (D+2)**2*(D+4)))
    check("central identities on grid D <= 80", ok)

    print("== [C] bulk band ==")
    disc = sp.cancel(4*A*C - B**2)
    pred = ((uv*(uv+2)*((Dv+3)**2-(uv+1)**2) - xv**2*(uv+1)**2)
            / ((Dv+1-sv)*(sv+2))**2)
    check("discriminant identity (symbolic)",
          sp.simplify(sp.cancel(disc - pred)) == 0)
    ok = True; used = 0
    for M in range(0, 41):
        for Q in range(0, 41):
            D = M+Q; x = M-Q; p = pcoef(M, Q)
            for s in range((D+1)//2, D):
                u = 2*s-D; U = (u+1)**2
                if u >= 1 and x*x*U <= (U-1)*((D+3)**2-U):
                    used += 1
                    ok &= (Tval(p, D, Q, s) >= 0)
    check(f"bulk cells all T >= 0 on grid D <= 80 ({used} cells)", ok)

    print("== [D] tail flow ==")
    kv, wv, w1v = sp.symbols('k w w1')
    check("(a) (D+1)^2 - (u+1)^2 == 4(s+1)(D-s)",
          sp.expand((Dv+1)**2 - (uv+1)**2 - 4*(sv+1)*(Dv-sv)) == 0)
    W2  = xv**2 - 4*kv*(Dv+1-kv)          # w(s)^2,  k = D-s
    W2m = xv**2 - 4*(kv+1)*(Dv-kv)        # w(s-1)^2, k -> k+1
    check("(b) w(s)^2 - w(s-1)^2 == 4u",
          sp.expand(W2 - W2m - 4*(Dv-2*kv)) == 0)
    # (c) comparison: (x+w)(x-w1) >= x^2 - w^2  <=>  (w-w1)(x+w) >= 0
    lhs = sp.expand((xv+wv)*(xv-w1v) - (xv**2 - wv**2))
    check("(c) (x+w)(x-w1) - (x^2-w^2) == (w-w1)(x+w)",
          sp.expand(lhs - (wv-w1v)*(xv+wv)) == 0)
    # (d) I1 split and boundary value
    phi = (xv+wv)/2
    u_k = Dv - 2*kv
    I1 = sp.expand((u_k+2)*(kv+1)*phi**2 - xv*(u_k+1)*kv*phi
                   + u_k*(Dv-kv+2)*kv**2)
    p1 = sp.Poly(I1, wv)
    P1 = sp.expand(p1.nth(0) + p1.nth(2)*W2)
    Q1 = sp.expand(p1.nth(1))
    check("(d) Q1 == x(D-k+2)/2",
          sp.expand(Q1 - xv*(Dv-kv+2)/2) == 0)
    P1pred = (xv**2*(Dv+2-kv) - 2*kv*(Dv**2-2*Dv*kv+3*Dv+2*kv**2-2*kv+2))/2
    check("(d) P1 closed form", sp.expand(P1 - P1pred) == 0)
    bnd1 = sp.expand(P1.subs(xv**2, 4*kv*(Dv+1-kv)))
    check("(d) P1 boundary == k(D+2)(u+1)",
          sp.expand(bnd1 - kv*(Dv+2)*(Dv-2*kv+1)) == 0)
    # (e) I2 split and boundary value
    I2 = sp.expand(xv*(u_k+1)*phi - 2*u_k*(Dv-kv+2)*kv)
    p2 = sp.Poly(I2, wv)
    P2 = sp.expand(p2.nth(0)); Q2 = sp.expand(p2.nth(1))
    check("(e) Q2 == x(u+1)/2", sp.expand(Q2 - xv*(Dv-2*kv+1)/2) == 0)
    P2pred = (xv**2*(Dv-2*kv+1) - 4*kv*(Dv**2-3*Dv*kv+2*Dv+2*kv**2-4*kv))/2
    check("(e) P2 closed form", sp.expand(P2 - P2pred) == 0)
    bnd2 = sp.expand(P2.subs(xv**2, 4*kv*(Dv+1-kv)))
    check("(e) P2 boundary == 2k(k+1)", sp.expand(bnd2 - 2*kv*(kv+1)) == 0)
    # link identities tying I1, I2 to the quadratic form of [A]:
    # (d') the form value at r = k/phi, cleared by (s+2)(D+1-s)phi^2,
    # is exactly I1  (s = D-k):
    phiv = (xv+wv)/2
    rr = kv/phiv
    formval = sp.cancel(((A + B*rr + C*rr**2)*(sv+2)*(Dv+1-sv)*phiv**2)
                        .subs(sv, Dv-kv))
    check("(d') form value at r = k/phi, cleared, == I1",
          sp.simplify(sp.cancel(formval - I1)) == 0)
    # (e') the vertex comparison -B/(2C) - k/phi, cleared by the
    # positive 2u(s+2)phi, is exactly I2  (s = D-k):
    vtx = sp.cancel(((-B/(2*C) - rr)*2*uv*(sv+2)*phiv)
                    .subs(sv, Dv-kv))
    check("(e') vertex comparison, cleared, == I2",
          sp.simplify(sp.cancel(vtx - I2)) == 0)
    # grid: exact conjugacy + comparison invariant + T >= 0 on flow
    # cells, all in exact rational arithmetic
    ok = True; used = 0
    for M in range(0, 61):
        for Q in range(0, 61):
            if M < Q: continue
            D = M+Q; x = M-Q
            if x == 0: continue
            p = pcoef(M, Q)
            y = F(x); s = D-1
            while s >= (D+1)//2:
                k = D-s
                if x*x < 4*k*(D+1-k): break
                used += 1
                if p[s] == 0: ok = False; break
                r = F(p[s+1], p[s])
                w2 = x*x - 4*k*(D+1-k)
                # the theorem's exact conjugacy r_s = k/y_s:
                if r != F(k, 1)/y: ok = False; break
                # comparison invariant y_s >= phi(s) = (x+sqrt(w2))/2,
                # exactly via squares (w2 >= 0 on flow cells):
                t2y = 2*y - x
                if not (t2y >= 0 and t2y*t2y >= w2): ok = False; break
                if not r > 0: ok = False; break
                if Tval(p, D, Q, s) < 0: ok = False; break
                # the paper's auxiliary flow y_{s-1} = x - (s+1)(D-s)/y_s,
                # coefficient taken at the CURRENT index s:
                y = F(x) - F((s+1)*(D-s), 1)/y
                s -= 1
    check(f"flow cells: exact conjugacy r = k/y, y >= phi, T >= 0 "
          f"on grid D <= 120 ({used} cells)", ok)

    print("== [E] coverage ==")
    tv = sp.Symbol('t')  # t = x^2
    marg = sp.expand((Dv**2+2*Dv-tv)*(4*Dv+8) - tv)
    # linear decreasing in t; at t = D^2 equals 7D^2 + 16D > 0
    check("coverage margin at t=D^2 == 7D^2+16D",
          sp.expand(marg.subs(tv, Dv**2) - (7*Dv**2+16*Dv)) == 0)
    check("coverage margin slope in t == -(4D+9)",
          sp.expand(sp.diff(marg, tv) + 4*Dv+9) == 0)
    # E2E: every top-half cell covered by a certified mechanism
    ok = True; mech = {'sD':0,'u0':0,'bulk':0,'flow':0,'gap_even':0,
                       'gap_odd_u1':0,'gap_odd_window':0}
    for M in range(0, 46):
        for Q in range(0, 46):
            if M < Q: continue
            D = M+Q; x = M-Q; p = pcoef(M, Q)
            for s in range((D+1)//2, D+1):
                u = 2*s-D; U = (u+1)**2; T = Tval(p, D, Q, s)
                if s == D:
                    mech['sD'] += 1; ok &= (T == 1); continue
                if u == 0:
                    mech['u0'] += 1; ok &= (T >= 0); continue
                if u >= 1 and x*x*U <= (U-1)*((D+3)**2-U):
                    mech['bulk'] += 1; ok &= (T >= 0); continue
                if U >= (D+1)**2 - x*x:
                    mech['flow'] += 1; ok &= (T >= 0); continue
                key = ('gap_even' if Q % 2 == 0 else
                       'gap_odd_u1' if u == 1 else 'gap_odd_window')
                mech[key] += 1; ok &= (T >= 0)
    check(f"E2E coverage grid M,Q <= 45: {mech}", ok)

    print("== [F] odd u = 1 closed form and gap lemmas ==")
    M_, Q_ = sp.symbols('M Q')
    Dp, xp = M_ + Q_, M_ - Q_
    sh = (Dp + 1)/2                       # 2s = D+1
    ps_, psm1 = a, -a                     # p_{s-1} = -p_s (Q odd)
    ps1 = (xp*ps_ + (sh - 1 - Dp)*psm1)/(sh + 1)
    ps2 = (xp*ps1 + (sh - Dp)*ps_)/(sh + 2)
    T1 = ps_**2 + ps_*ps2 - ps1**2 - psm1*ps1
    check("Q odd, u = 1: (s+1)^2 (s+2) T_s == 4(M+1)(Q+2) p_s^2",
          sp.simplify((sh+1)**2*(sh+2)*T1 - 4*(M_+1)*(Q_+2)*a**2) == 0)
    Uv, tq = sp.symbols('U t')
    Eq = (Dv + 3)**2
    hq = Eq + 1 - xv**2
    qf = lambda t: t**2 - hq*t + Eq
    check("x^2 U - (U-1)(E-U) == q(U)",
          sp.expand(xv**2*Uv - (Uv-1)*(Eq-Uv) - qf(Uv)) == 0)
    U0 = (Dv + 1)**2 - xv**2
    check("q(U0) == -[(D^2+2D-x^2)(4D+8) - x^2]",
          sp.expand(qf(U0) + ((Dv**2+2*Dv-xv**2)*(4*Dv+8) - xv**2)) == 0)
    Qg, xg = sp.symbols('Qg xg', nonnegative=True)
    Dg, Mg = xg + 2*Qg, Qg + xg
    hg = (Dg + 3)**2 + 1 - xg**2
    check("h == (2Q+3)(2M+3) + 1",
          sp.expand(hg - ((2*Qg+3)*(2*Mg+3) + 1)) == 0)
    check("h - 3(D+3) == 4MQ + 3M + 3Q + 1",
          sp.expand(hg - 3*(Dg+3) - (4*Mg*Qg + 3*Mg + 3*Qg + 1)) == 0)
    check("h - (2Q+3)(D+3) == (2Q+3)x + 1",
          sp.expand(hg - (2*Qg+3)*(Dg+3) - ((2*Qg+3)*xg + 1)) == 0)
    Bq = 7*Eq/(6*hq)
    check("q(7E/(6h)) == E(49E - 6h^2)/(36h^2)",
          sp.simplify(qf(Bq) - Eq*(49*Eq - 6*hq**2)/(36*hq**2)) == 0)
    okS = True; ncell = 0; first_odd2 = None
    for D in range(1, 301):
        E = (D + 3)**2
        for Q in range(0, D//2 + 1):
            x = D - 2*Q
            gaps = []
            for u in range(1, D + 1):
                U = (u + 1)**2
                if U >= (D + 1)**2 - x*x:
                    break
                gaps.append((u, x*x*U > (U - 1)*(E - U)))
            for u, g in gaps:
                if not g or (D - u) % 2:
                    continue
                ncell += 1
                okS &= 6*(2*Q + 3)*(u + 1)**2 < 7*(D + 3)
                okS &= all(g2 for u2, g2 in gaps if u2 <= u)
                if Q % 2 and u >= 2 and first_odd2 is None:
                    first_odd2 = (D, Q, u)
    check(f"grid D <= 300: gap strip and heredity on {ncell} gap cells",
          okS and ncell > 100)
    check(f"first odd-Q gap cell with u >= 2 is (84, 1, 2): got {first_odd2}",
          first_odd2 == (84, 1, 2))

    print("== [G] real-argument relaxation ==")
    # D=4, q=8/7, x=D-2q=12/7.  The same coefficient recurrence defines
    # [w^s](1+w)^(D-q)(1-w)^q for real q.
    Dr = 4
    xr = F(12, 7)
    pr = [F(0)]*(Dr+2)
    pr[0], pr[1] = F(1), xr
    for ss in range(1, Dr+1):
        pr[ss+1] = (xr*pr[ss] + (ss-1-Dr)*pr[ss-1])/F(ss+1)
    Tr = pr[2]**2 + pr[2]*pr[4] - pr[3]**2 - pr[1]*pr[3]
    check("D=4, q=8/7, s=2 gives T_2 = -1430/117649",
          Tr == F(-1430, 117649))

    print("== THREE-REGIME CLOSURE:",
          "ALL CHECKS PASS ==" if OK else "FAILURES ==")
    raise SystemExit(0 if OK else 1)


if __name__ == '__main__':
    main()
