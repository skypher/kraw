#!/usr/bin/env python3
"""Exact checks for the bulk, center, tail-flow, coverage, and
small-offset reflection arguments.

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

REFLECTION COLLAPSE (gap closed for u <= 3).
Reflection p_{D-j} = (-1)^Q p_j pins the chain: with s = (D+u)/2,
a = p_{s-u}, the constraint p_s = (-1)^Q a forces p_{s-u+1}/a, and
T_s = R_u(M,Q) a^2 with explicit R_u; for u <= 3 the numerators are
manifestly PSD, the collapse denominators do not vanish on the gap,
and a != 0 automatically.  So gap cells with u <= 3 are closed.

REMAINING SET: gap cells with u >= 4 and Q >= 3 start at D = 442
(census below); those cells are closed by the finite-gap-offsets and
later certificates, which consume this census as the input to their
sector bound M >= 425.

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
[E] coverage margin polynomial > 0; E2E grid D <= 90: every top-half
    cell is covered by a certified mechanism (no fallback).
[F] collapse identities and PSD numerators for u <= 3; beta != 0 on
    the gap; first open cell census.
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
    ok = True; mech = {'sD':0,'u0':0,'bulk':0,'flow':0,'gap3':0,'open':0}
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
                if u <= 3:
                    mech['gap3'] += 1; ok &= (T >= 0); continue
                mech['open'] += 1
    check(f"E2E coverage grid D <= 90: {mech}", ok and mech['open'] == 0)

    print("== [F] reflection collapse, u <= 3 ==")
    M_, Q_ = sp.symbols('M Q')
    # Verify the full closed form R = num/den, not a ratio defined to
    # cancel. Each entry is the exact rational
    # function; the check is simplify(R - num/den) == 0, and the
    # denominator's positivity (product of squares and positive
    # linear factors) is certified structurally.
    Dp = M_ + Q_
    hard_full = {
        (1, 1):  (32*(M_+2)*(Q_+1), (Dp+3)**2*(Dp+5)),
        (1, -1): (32*(M_+1)*(Q_+2), (Dp+3)**2*(Dp+5)),
        (2, 1):  (16*(M_+1)*(Q_+1)*(3*M_**2-2*M_*Q_+6*M_+3*Q_**2+6*Q_),
                  (M_-Q_)**2*(Dp+4)**2*(Dp+6)),
        (2, -1): (32*(M_+2)*(Q_+2), (Dp+4)**2*(Dp+6)),
        (3, 1):  (64*(M_+2)*(Q_+1)*(M_**2-2*M_*Q_+5*Q_**2+12*Q_-1),
                  (M_-3*Q_-1)**2*(Dp+5)**2*(Dp+7)),
        (3, -1): (64*(M_+1)*(Q_+2)*(5*M_**2-2*M_*Q_+12*M_+Q_**2-1),
                  (Dp+5)**2*(Dp+7)*(3*M_-Q_+1)**2),
    }
    okF = True
    for u in (1, 2, 3):
        for eps in (1, -1):
            pch = {0: a, 1: b}
            for i in range(1, u+3):
                j = (Dv+u)/2 - u + i
                pch[i+1] = sp.cancel((xv*pch[i] + (j-1-Dv)*pch[i-1])/(j+1))
            bs = sp.solve(sp.expand(pch[u] - eps*a), b)[0]
            ps1 = sp.cancel(pch[u+1].subs(b, bs))
            ps2 = sp.cancel(pch[u+2].subs(b, bs))
            psm = sp.cancel(pch[u-1].subs(b, bs))
            T = sp.cancel(a**2 + eps*a*ps2 - ps1**2 - psm*ps1)
            R = sp.cancel(T/a**2).subs({Dv: M_+Q_, xv: M_-Q_})
            hn, hd = hard_full[(u, eps)]
            # full-form equality (non-vacuous): R == hn/hd exactly:
            okF &= sp.simplify(sp.cancel(R - hn/hd)) == 0
            # denominator sign: hd is (positive constant) x (positive
            # factors) x squares; its non-square factors are (D+c),
            # c > 0 => hd > 0 in range (its square factors can vanish
            # only on the beta-locus, handled below):
            dconst, dfacs = sp.factor_list(hd)
            okF &= (dconst.is_number and dconst > 0)
            for f, mult in dfacs:
                pf = sp.Poly(f, M_, Q_)
                deg = pf.total_degree()
                okF &= (mult % 2 == 0) or (
                    deg == 1 and pf.nth(1, 0) >= 0 and pf.nth(0, 1) >= 0
                    and pf.nth(0, 0) > 0)
            # numerator PSD certificates:
            if (u, eps) == (2, 1):
                q = 3*M_**2-2*M_*Q_+6*M_+3*Q_**2+6*Q_
                okF &= sp.expand(q - ((M_-Q_)**2+2*M_**2+2*Q_**2+6*M_+6*Q_)) == 0
            if (u, eps) == (3, 1):
                q = M_**2-2*M_*Q_+5*Q_**2+12*Q_-1
                okF &= sp.expand(q - ((M_-Q_)**2+4*Q_**2+12*Q_-1)) == 0
            if (u, eps) == (3, -1):
                q = 5*M_**2-2*M_*Q_+12*M_+Q_**2-1
                okF &= sp.expand(q - ((M_-Q_)**2+4*M_**2+12*M_-1)) == 0
    check("collapse FULL closed forms R == num/den (non-vacuous) + "
          "denominator sign + PSD rewrites (symbolic)", okF)
    # beta != 0 on gap for u <= 3: only nontrivial loci are x = 0 (u=2,+)
    # and M-3Q-1 = 0 (u=3,+).  x = 0 fails the gap inequality trivially;
    # for M = 3Q+1 (x = 2Q+1, D = 4Q+1) check 16 x^2 <= 15((D+3)^2-16):
    Qs = sp.Symbol('Qs', nonnegative=True)
    expr = sp.expand(15*((4*Qs+4)**2-16) - 16*(2*Qs+1)**2)
    # = 176 Qs^2 + 416 Qs - 16 >= 0 for Qs >= 1; Qs = 0 => M=1,Q=0 => D=1 < 3
    check("u=3 beta-locus outside gap: 176Q^2+416Q-16 form",
          sp.expand(expr - (176*Qs**2+416*Qs-16)) == 0)
    # Census the first gap cell with u >= 4. Report both the Q >= 3
    # residual range (the Q <= 2 range is handled separately) and the
    # first cell when all Q are included.
    def first_gap(Qlo):
        for D in range(2, 1500):
            E = (D+3)**2
            for Q in range(Qlo, D//2+1):
                x = D-2*Q
                for u in range(4, D+1):
                    if (D-u) % 2: continue
                    U = (u+1)**2
                    if U >= (D+1)**2 - x*x: break
                    if x*x*U > (U-1)*(E-U):
                        return (D, Q, u)
                    break
        return None
    firstc = first_gap(3)
    firstall = first_gap(0)
    check(f"first u>=4 gap cell with Q>=3 is (442,3,4): got {firstc}",
          firstc == (442, 3, 4))
    check(f"first u>=4 gap cell over ALL Q is (142,0,4) "
          f"[Q<=2 handled separately]: got {firstall}",
          firstall == (142, 0, 4))

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
