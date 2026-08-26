#!/usr/bin/env python3
"""Exact per-Q strip verification for 3 <= Q <= Q0, all u and D.

For fixed Q, normalizing T_s by C(M, s)^2 and
substituting s = (D+u)/2, M = D-Q gives the exact rational form
T = num/den, valid for u <= D - 2Q - 6
(binomial-ratio poles live at u > D - 2Q - 6; that edge is
flow-covered for D >= D_edge(Q), and everything below the onsets is
inside the D <= 1200 scan or a direct check here).

STRIP >= GAP (all Q): on the gap,
U- <= (7/6) E / h with h = (2Q+3)(2M+3)+1 >= 3(D+3) = 3 sqrt(E)
[since 1 + sqrt(1 - 4/9) > 12/7], so

    gap(u, Q)  ==>  u^2 <= (u+1)^2 <= 7(D+3) / (6(2Q+3)) =: BQ(D).

PER-Q CERTIFICATE on the strip {0 <= u, u^2 <= BQ(D)}:
  S_Q(u, D) := oriented numerator = sum_j c_j(D) u^j  (deg 2Q+1);
  after removing the common positive content, check
   - every negative c_j has j >= 2 and is PAIRED with the positive
     c_{j-2}:  c_{j-2}(D) - |c_j(D)| BQ(D) >= 0 for D >= D0
     (univariate exact: positive leading coefficient + Sturm
     root-count on [D0, oo)), each positive coefficient used at most
     once;
   - all unpaired coefficients are >= 0 for D >= D0 (same test);
  then S_Q >= 0 on the strip for D >= D0, since
  c_{j-2} u^{j-2} + c_j u^j = u^{j-2} (c_{j-2} + c_j u^2) >= 0.
  Cells with D < D0 = 2Q+6 are covered by the D <= 1200 scan, and the
  den < 0 orientation is certified on the strip 0 <= u <= D-2Q-6 by
  direct factorization: positive constant, (D+u+c) factors, exactly
  one odd-multiplicity negative factor u-D+c0 (c0 < 2Q+6), and
  even-multiplicity factors whose zero locus lies strictly above the
  strip (so the squares are strictly positive there).

Together with the off-gap results and the checks for u <= 14 and Q <= 2,
this verifies every cell through the first gap cell with Q > Q0 and
u > UMAX, every pair with min(M,Q) <= Q0, and every offset u <= UMAX.

CHECKS per Q: [den] orientation and square-nonvanishing on the strip,
[val] numeric identity at sample cells vs binomial p-values, [pair]
the pairing inequalities certified at the common onset D0 = 2Q+6 with
the partner pattern asserted against the manuscript formula
(4r, 4r+1 for even Q; 4r+2, 4r+3 for odd Q), [gap] strip >= gap
constants.  Finally [T] the threshold by exact scan from D = 4, with
the manuscript values (14827, 13, 15) asserted for the canonical
invocation Q0 = 12, UMAX = 14.

Usage: fixed-argument-strips.py [Q0=12] [UMAX=14]
"""
import sys
from math import comb
from math import isqrt
import os

import sympy as sp

from witness_io import WitnessWriter

OK = True
def check(name, cond):
    global OK
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}", flush=True)
    OK = OK and cond


def progress(Q, phase):
    """Deterministic algorithmic progress for the long exact certificates."""
    print(f"  [progress] Q={Q}: {phase}", flush=True)


Dv, uv = sp.symbols('D u')
Mv, sv = sp.symbols('M s')


def strip_form(Q):
    def prat(j):
        tot = 0
        for b_ in range(Q+1):
            progress(Q, f"ratio shift {j:+d}, term {b_+1}/{Q+1}")
            d = j - b_
            r = sp.Integer(1)
            if d >= 0:
                for i in range(d):
                    r *= (Mv - sv - i)/(sv + i + 1)
            else:
                for i in range(-d):
                    r *= (sv - i)/(Mv - sv + i + 1)
            tot += (-1)**b_*sp.binomial(Q, b_)*r
        progress(Q, f"ratio shift {j:+d}, normalize exact sum")
        together = sp.together(tot)
        progress(Q, f"ratio shift {j:+d}, cancel exact sum")
        return sp.cancel(together)
    progress(Q, "construct four shifted coefficient ratios")
    r0 = prat(0)
    r2 = prat(2)
    r1 = prat(1)
    rm1 = prat(-1)
    progress(Q, "combine and cancel the left determinant pair")
    left = sp.cancel(r0**2 + r0*r2)
    progress(Q, "combine and cancel the right determinant pair")
    right = sp.cancel(r1**2 + rm1*r1)
    progress(Q, "combine and cancel the determinant difference")
    T = sp.cancel(left - right)
    num, den = sp.fraction(T)
    progress(Q, "substitute the fixed-Q strip coordinates in the numerator")
    num = sp.expand(num.subs({sv: (Dv+uv)/2, Mv: Dv-Q}))
    progress(Q, "substitute the fixed-Q strip coordinates in the denominator")
    den = sp.together(den.subs({sv: (Dv+uv)/2, Mv: Dv-Q}))
    if den.subs({uv: 5, Dv: 10**6}) > 0:
        num, den = -num, -den
    # The raw pair (num, den) is simultaneously negated when needed so that
    # den < 0. Returning S := -num then writes T = S/(-den), which matches
    # the positive-denominator convention of Lemma 4.4.
    return sp.expand(-num), den, {
        -1: rm1, 0: r0, 1: r1, 2: r2,
    }


def den_negative(den, Q):
    """Certify den < 0 on the strip 0 <= u <= D-2Q-6, D >= 2Q+6.

    Every factor must be linear.  Factors u+D+c0 (c0 > 0) are positive on
    the strip.  Factors u-D+c0 with c0 < 2Q+6 are negative there (at
    u = D-2Q-6 the value is c0-2Q-6 < 0) and their zero u = D-c0 lies
    strictly above the strip, so even multiplicities of such factors are
    strictly positive on the strip -- this covers the squared binomial-
    ratio denominators.  D-only factors are certified positive at
    D = 2Q+6 with positive slope.  Overall sign is negative iff the count
    of odd-multiplicity negative factors is odd (the data has exactly
    one, u-D-2, but any odd count is accepted)."""
    const, facs = sp.factor_list(den)
    negodd = 0
    if not (const.is_number and const > 0):
        return False
    for f, mult in facs:
        pf = sp.Poly(f, uv, Dv)
        if pf.total_degree() != 1:
            return False
        au, ad, c0_ = pf.nth(1, 0), pf.nth(0, 1), pf.nth(0, 0)
        if au == 0:
            if ad > 0 and ad*(2*Q + 6) + c0_ > 0:
                continue
            return False
        if au == 1 and ad == 1 and c0_ > 0:
            continue
        if au == 1 and ad == -1 and c0_ < 2*Q + 6:
            if mult % 2:
                negodd += 1
            continue
        return False
    return negodd % 2 == 1


def positive_for_D(expr, D0):
    """expr(D) > 0 for all D >= D0: LC > 0, no roots >= D0, value > 0."""
    pe = sp.Poly(sp.expand(expr), Dv)
    if pe.degree() < 0 or pe.LC() <= 0:
        return False
    return pe.count_roots(D0, sp.oo) == 0 and pe.eval(D0) > 0


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


def first_open_gap(qmin, umax, dstart, dstop):
    """Return the first (D,Q,u) with Q >= qmin and u > umax.

    The gap is U < U_-, so only the first parity-compatible u above umax
    need be considered.  At fixed (D,u), x=D-2Q has parity D, and the gap
    inequalities are exactly

        ((U-1)(E-U))/U < x^2 < (D+1)^2-U.

    Reductions used, both proved in the manuscript: (i) gap heredity --
    U_- does not depend on u, so if the first parity-compatible u above
    umax admits no gap cell at any x, no larger u does; (ii) the left
    inequality is monotone increasing in x^2, so testing the largest
    admissible parity-compatible x decides existence for all Q >= qmin.
    """
    for D in range(dstart, dstop):
        u = umax + 1
        if (D - u) % 2:
            u += 1
        if u > D:
            continue
        U = (u + 1)**2
        E = (D + 3)**2
        upper = (D + 1)**2 - U
        if upper <= 0:
            continue
        x = min(D - 2*qmin, isqrt(upper - 1))
        if x < 0:
            continue
        if (x - D) % 2:
            x -= 1
        if x >= 0 and x*x*U > (U - 1)*(E - U):
            return D, (D - x)//2, u
    return None


def certify_Q(Q, witness=None):
    progress(Q, "begin exact strip-form construction")
    S, den, ratios = strip_form(Q)
    progress(Q, "certify denominator orientation and nonvanishing")
    if not den_negative(den, Q):
        return False, f"Q={Q}: den orientation fails"
    progress(Q, "extract the oriented numerator as a polynomial in u")
    P = sp.Poly(sp.nsimplify(S), uv)
    degu = P.degree()
    if degu != 2*Q+1:
        return False, f"Q={Q}: unexpected deg_u {degu}"
    # strip common positive content in D: gcd of coefficients
    coeffs = [sp.expand(P.nth(j)) for j in range(degu+1)]
    progress(Q, f"compute common D-content of {degu+1} coefficients")
    g = sp.gcd([c for c in coeffs if c != 0])
    # g must be positive for D >= some small D0g:
    D0g = 2*Q + 4
    if not positive_for_D(g, D0g):
        g2 = sp.expand(-g)
        if positive_for_D(g2, D0g):
            g = g2
            coeffs = [sp.expand(-c) for c in coeffs]
        else:
            return False, f"Q={Q}: content not sign-definite"
    cc = [sp.cancel(c/g) for c in coeffs]
    # classify signs at large D
    sgn = []
    for j, c in enumerate(cc):
        progress(Q, f"classify leading sign of coefficient {j}/{degu}")
        if c == 0:
            sgn.append(0); continue
        pe = sp.Poly(sp.expand(c), Dv)
        sgn.append(1 if pe.LC() > 0 else -1)
    if sgn[degu] != 1 or (degu >= 1 and sgn[degu-1] not in (0, 1)):
        return False, f"Q={Q}: top coefficients not positive"
    BQ = sp.Rational(7, 6)*(Dv+3)/(2*Q+3)
    used = set()
    pairing_rows = []
    D0 = 2*Q + 6          # the manuscript's common onset; no fallback
    if witness:
        sname = f"fixed_Q{Q}_S"
        dname = f"fixed_Q{Q}_den"
        gname = f"fixed_Q{Q}_content"
        witness.poly(sname, S, (Dv, uv))
        witness.poly(dname, den, (Dv, uv))
        witness.poly(gname, g, (Dv,))
        witness.meta("FIXED_CASE", Q, D0, D0g, degu,
                     sname, dname, gname)
        den_const, den_factors = sp.factor_list(den)
        den_const = sp.Rational(den_const)
        witness.meta("DEN_CONST", Q, int(den_const.p), int(den_const.q))
        for factor_index, (factor, multiplicity) in enumerate(den_factors):
            fname = f"fixed_Q{Q}_den_factor_{factor_index}"
            witness.poly(fname, factor, (Dv, uv))
            witness.meta("DEN_FACTOR", Q, fname, multiplicity)
        for j, coefficient in enumerate(cc):
            cname = f"fixed_Q{Q}_c{j}"
            witness.poly(cname, coefficient, (Dv,))
            witness.meta("FIXED_COEFF", Q, j, cname)
        for shift, ratio in sorted(ratios.items()):
            ratio_num, ratio_den = sp.fraction(sp.cancel(ratio))
            ratio_num = sp.expand(ratio_num.subs(
                {sv: (Dv+uv)/2, Mv: Dv-Q}))
            ratio_den = sp.expand(ratio_den.subs(
                {sv: (Dv+uv)/2, Mv: Dv-Q}))
            shift_name = "m1" if shift == -1 else f"p{shift}"
            nname = f"fixed_Q{Q}_ratio_{shift_name}_num"
            dname_ratio = f"fixed_Q{Q}_ratio_{shift_name}_den"
            witness.poly(nname, ratio_num, (Dv, uv))
            witness.poly(dname_ratio, ratio_den, (Dv, uv))
            witness.meta("FIXED_RATIO", Q, shift, nname, dname_ratio)
    # The termwise bound c_{j-2} u^{j-2} + c_j u^j =
    # u^{j-2}(c_{j-2} + c_j u^2) >= 0 on the strip u^2 <= BQ needs,
    # for c_j < 0, BOTH: (i) c_{j-2} + c_j BQ >= 0 (the linear-in-u^2
    # form nonneg at the right endpoint) AND (ii) c_j <= 0 on
    # [D0, oo) so the form is DECREASING in u^2 and the endpoint is
    # its min.  Certify BOTH exactly (LC-sign classification is not
    # enough on a finite-then-infinite ray).  The manuscript claims the
    # COMMON onset D0 = 2Q+6 for every pair and every unpaired
    # coefficient; certify exactly that -- a family needing a later
    # onset is a FAIL, not a silent fallback.
    def neg_on_ray(expr, D0_):
        pe = sp.Poly(sp.expand(expr), Dv)
        if pe.degree() < 0:
            return True
        return (-pe).LC() > 0 and pe.count_roots(D0_, sp.oo) == 0 \
            and pe.eval(D0_) < 0
    for j in range(degu+1):
        if sgn[j] >= 0:
            continue
        progress(Q, f"pair negative coefficient c_{j} with c_{j-2}")
        if j < 2 or sgn[j-2] != 1 or (j-2) in used:
            return False, f"Q={Q}: negative c_{j} unpairable"
        used.add(j-2)
        expr = sp.together(cc[j-2] + cc[j]*BQ)
        exprn = sp.expand(sp.numer(expr)*sp.denom(expr))
        # (i) endpoint form >= 0, (ii) c_j <= 0, (iii) c_{j-2} >= 0
        # -- all on [D0, oo); (iii) makes the u = 0 value nonneg
        # too (belt-and-braces: it is implied by (i)+(ii) but we
        # certify it directly per M2):
        progress(Q, f"pair ({j-2},{j}): endpoint Sturm certificate")
        endpoint_ok = positive_for_D(exprn, D0)
        progress(Q, f"pair ({j-2},{j}): negative-slope Sturm certificate")
        negative_ok = neg_on_ray(cc[j], D0)
        progress(Q, f"pair ({j-2},{j}): positive-partner Sturm certificate")
        partner_ok = positive_for_D(cc[j-2], D0)
        if not (endpoint_ok and negative_ok and partner_ok):
            return False, (f"Q={Q}: pair ({j-2},{j}) sign facts "
                           f"fail at the common onset D0={D0}")
        pairing_rows.append(f"{j-2}->{j}@{D0}")
    # the partner indices must match the manuscript's pattern:
    # 4r, 4r+1 (0 <= r < Q/2) for even Q; 4r+2, 4r+3 (0 <= r < (Q-1)/2)
    # for odd Q:
    if Q % 2 == 0:
        expected = {4*r + t for r in range(Q//2) for t in (0, 1)}
    else:
        expected = {4*r + t for r in range((Q-1)//2) for t in (2, 3)}
    if used != expected:
        return False, (f"Q={Q}: partner pattern {sorted(used)} != "
                       f"manuscript formula {sorted(expected)}")
    # every non-negatively-signed coefficient must be >= 0 on [D0,oo)
    # EXACTLY (LC > 0 is necessary, not sufficient) -- including the
    # ones consumed as a pair partner (their >= 0 is used at u = 0):
    for j in range(degu+1):
        if sgn[j] != 1:
            continue
        progress(Q, f"coefficient c_{j}: nonnegative-ray Sturm certificate")
        if not positive_for_D(cc[j], D0):
            return False, (f"Q={Q}: coefficient c_{j} not >= 0 at the "
                           f"common onset D0={D0}")
    D0max = D0
    # numeric identity spot check; a vacuous run (no admissible
    # cells) is a failure, not a silent pass
    okn = True
    nspot = 0
    for M0 in (2*Q+40, 2*Q+61):
        progress(Q, f"numeric identity row M={M0}")
        D = M0 + Q
        p = pcoef(M0, Q)
        for s in ((D+1)//2 + 1, (D+1)//2 + 3):
            u = 2*s - D
            if u < 0 or u > D - 2*Q - 6:
                continue
            lhs = Tval(p, D, Q, s)
            Sv = S.subs({uv: u, Dv: D})
            dv = den.subs({uv: u, Dv: D})
            okn &= (sp.Integer(lhs)
                    == sp.nsimplify(sp.Rational(-Sv, 1)/dv*comb(M0, s)**2))
            nspot += 1
    if not okn or nspot < 1:
        return False, f"Q={Q}: numeric identity fails ({nspot} cells)"
    pair_text = ",".join(pairing_rows) if pairing_rows else "none"
    return True, (f"Q={Q}: OK deg={degu} D0={D0max}; "
                  f"pairs[{pair_text}]")


def main():
    Q0 = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    UMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 14
    witness_path = os.environ.get("KRAW_EXPORT_WITNESS")
    witness = (WitnessWriter(witness_path, "fixed-argument")
               if witness_path else None)
    printed_edge_onsets = {
        3: 31, 4: 38, 5: 45, 6: 52, 7: 59,
        8: 66, 9: 73, 10: 80, 11: 86, 12: 93,
    }

    print("== [gap] strip >= gap constants ==")
    # U- <= (7/6) E/h needs h >= 2 sqrt(E) * 6/7... precisely:
    # U- = 2E/(h + sqrt(h^2-4E)) and h >= 3 sqrt(E) =>
    # h + sqrt(h^2-4E) >= 3sqrt(E)(1 + sqrt(1 - 4/9)) = 3(1+sqrt5/3)sqrtE
    # >= (12/7) * ... : check 2/(3(1+sqrt(5)/3)) <= 7/6*(1/3)*3... i.e.
    # 2E/(3sqrtE (1+sqrt(5)/3)) <= (7/6) E/(3 sqrt E) <=> 2/(3+sqrt5)
    # <= 7/18 <=> 36 <= 7(3+sqrt5):
    check("2/(3+sqrt5) <= 7/18  (36 <= 21 + 7 sqrt5)",
          sp.simplify(21 + 7*sp.sqrt(5) - 36 > 0) == True)
    Mcheck, Qcheck = sp.symbols('Mcheck Qcheck', nonnegative=True)
    h_margin = sp.Poly(sp.expand(
        (2*Qcheck+3)*(2*Mcheck+3)+1 - 3*(Mcheck+Qcheck+3)),
        Mcheck, Qcheck)
    check("h >= 3 sqrt(E): (2Q+3)(2M+3)+1 >= 3(D+3)",
          all(c >= 0 for c in h_margin.coeffs()))

    print(f"== per-Q strip certificates, Q = 3..{Q0} ==")
    for Q in range(3, Q0+1):
        print(f"  [progress] fixed argument Q={Q}/{Q0}", flush=True)
        ok, msg = certify_Q(Q, witness)
        # top edge v = D-u < 2Q+6: flow-covered once
        # (D-2Q-5)^2 >= U0 = (2Q+1)(2D-2Q+1), from D_edge(Q) <= 1200 on:
        Dw = sp.Symbol('Dw')
        edge = sp.expand((Dw-2*Q-5)**2 - (2*Q+1)*(2*Dw-2*Q+1))
        pe = sp.Poly(edge, Dw)
        onset = next(
            (d0 for d0 in range(2*Q+6, 1201)
             if pe.eval(d0) >= 0 and pe.count_roots(d0, sp.oo) == 0),
            None)
        onset_matches_text = (
            Q not in printed_edge_onsets or onset == printed_edge_onsets[Q])
        if witness and onset is not None:
            ename = f"fixed_Q{Q}_edge"
            witness.poly(ename, edge, (Dw,))
            witness.meta("EDGE_RAY", Q, ename, onset)
        check(f"{msg}; edge-flow exact onset={onset}",
              ok and pe.LC() > 0 and onset is not None
              and onset_matches_text)
        if witness and ok and onset is not None and onset_matches_text:
            witness.checkpoint(f"Q{Q}")

    print("== [T] new threshold ==")
    # exact scan from D = 4: no external premise about small D
    threshold_witness = first_open_gap(Q0+1, UMAX, 4, 200000)
    print(f"  first open gap cell (Q > {Q0}, u > {UMAX}): {threshold_witness}")
    if threshold_witness is None:
        check("threshold census found a first open cell", False)
        thr = None
    else:
        thr = threshold_witness[0]
        if (Q0, UMAX) == (12, 14):
            # the manuscript's census values are asserted, not just
            # printed:
            check(f"threshold census matches manuscript: {threshold_witness} == "
                  f"(14827, 13, 15); m* = {thr-1}",
                  threshold_witness == (14827, 13, 15))
        else:
            check(f"threshold census is nonempty; m* = {thr-1}", True)

    print("== FIXED ARGUMENT STRIPS:", "ALL CHECKS PASS ==" if OK else
          "FAILURES ==")
    if OK and thr is not None:
        print(f"  => min(M,Q) <= {Q0} and offsets u <= {UMAX} are verified for all D,")
        print(f"     and every cell is verified for D <= {thr-1}")
        print(f"     (together with the companion regime, offset, "
              f"small-argument, and scan verifiers).")
        if witness:
            witness.meta("THRESHOLD", Q0 + 1, UMAX,
                         threshold_witness[0], threshold_witness[1],
                         threshold_witness[2])
            witness.finish()
    raise SystemExit(0 if OK else 1)


if __name__ == '__main__':
    main()
