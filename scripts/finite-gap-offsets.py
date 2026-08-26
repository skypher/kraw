#!/usr/bin/env python3
"""Exact verification for the finite family of gap offsets u=4..UMAX.

Setting: p_s = [w^s](1+w)^M (1-w)^Q, D = M+Q,
x = M-Q >= 0 WLOG, u = 2s-D, T_s the three-term expression;
The bulk/flow decomposition leaves open only the central gap
  GAP = { u >= 1 : x^2 U > (U-1)(E-U), U < (D+1)^2-x^2 },
  U = (u+1)^2, E = (D+3)^2,
and reflection closes gap cells with u <= 3.  Here we close
u = 4..UMAX via REFLECTION-CONSTRAINED QUADRATIC FORMS, fraction-free.

MECHANISM (per u, eps = (-1)^Q).  Let s = (D+u)/2, k0 = s-u = D-s.
Scaled chain P_i = c_i p_{k0+i}, c_{-1} = c_0 = 1,
c_{i+1} = c_i (k0+i+1):
  P_{i+1} = x P_i + (k0+i-1-D)(c_i/c_{i-1}) P_{i-1},
polynomial in (D, x) and linear in the two seeds.  T_s is a quadratic
form in the seeds with polynomial coefficients after scaling by the
positive quantity c_{u+1} c_{u+2}:
  Ttil := T_s c_{u+1} c_{u+2} = QF(seed1, seed2).
V1: seeds (a, b) = (p_{k0}, p_{k0+1}); reflection p_s = eps p_{k0}
    gives the linear constraint lam*a + mu*b = 0 with
    lam = coeff_a(P_u) - eps c_u, mu = coeff_b(P_u).  Pure algebra:
        Ttil * mu^2 = G1 * a^2,
        G1 = A mu^2 - B lam mu + C lam^2   (A, B, C from QF).
V2: seeds (a2, a) = (p_{k0-1}, p_{k0}); reflection
    p_{s+1} = eps p_{k0-1} gives lam2*a2 + mu2*a = 0 with
    lam2 = coeff_{a2}(P_{u+1}) - eps c_{u+1}, mu2 = coeff_a(P_{u+1}),
        Ttil * mu2^2 = G2 * a2^2.
Both identities hold at every cell satisfying the corresponding pinning
constraint.  After stripping a common factor g, G=g^2 G', division is
valid wherever g != 0; positivity of G' and nondegeneracy of the reduced
constraint close the cell.  At a zero of the first common factor g1, the
V2 pinning closes the cell: an exact resultant check proves that g1 and
the V2 common factor g2 have no simultaneous integer sector zero, and
the V2 reduced pair (lam2', mu2') is itself checked nondegenerate on
the sector -- both pinnings' reduced pairs get the full resultant
treatment, so the identity used is never 0 = 0.

SECTOR.  Gap cells with u >= 4 and Q >= 3 satisfy
  Q < M/(u+1)^2 <= M/25.
An exact census shows that none has D < 442, so
  M > (25/26)D >= (25/26)442 = 425;
since M is integral, M >= 426, while the later estimates require only
M >= 425.  It therefore suffices to certify G > 0 on
{M >= max(425, M0), 3 <= Q < M/(u+1)^2} via factorization and
per-factor top-form/domination:
  - linear factors: sign by corner checks;
  - core factors f: L(t) = top form of f at (1, t) positive on
    [0, 1/(u+1)^2] (exact 512-grid + derivative bound), then
    M-domination with t-weighted lower-degree sums S_j:
    f > 0 for M > M0 := min { M : sum_j S_j M^-j < L_lower }.
The generated onsets satisfy M0 <= 153, so cells with M <= M0 have
D < 163 and are covered by the exhaustive scan through D <= 1200.
Q <= 2 gap cells are covered by the per-Q certificates.

[S] SECTOR ESTIMATE.  Two ingredients, both certified in-script:
  (i) the analytic step: gap + Q >= 3 forces 2Q+3 < (D+3)/U + U/(D+3)
      with (D+3)/U > 8, whence Q < M/(u+1)^2 <= M/25;
  (ii) the exact census: no gap cell with u >= 4 and Q >= 3 has
      D < 442 (heredity-reduced integer scan, performed below --
      no external program is relied on), so on the sector
      M > D*(25/26) >= 442*25/26 = 425 >= 221.

CHECKS:
[S] the exact D < 442 census, plus the one nontrivial rational
    constant in the sector chain; the remaining steps of (i) are
    one-line algebra recorded in the comments and in the manuscript.
[G] per (u, eps, version): G > 0 certified on the sector; identity
    Ttil mu^2 == G a^2 verified SYMBOLICALLY (pure algebra) and
    NUMERICALLY at the first gap cells of EACH Q-parity (cell counts
    are reported and at least one cell per parity is required).
[T] final threshold: smallest D admitting a gap cell with
    u > UMAX, Q >= 3 (exact integer scan from D = 4) = the new
    unconditional D-threshold; every offset u <= UMAX is closed for
    all D.  For the canonical UMAX = 14 the manuscript census values
    (4587, 3, 15) are asserted, not just printed.

Usage: finite-gap-offsets.py [UMAX=14]
"""
import sys
import os
from fractions import Fraction as F
from math import comb
from math import isqrt

import sympy as sp

from witness_io import WitnessWriter

OK = True
def check(name, cond):
    global OK
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}", flush=True)
    OK = OK and cond


def progress_detail(message):
    """Emit replay progress without changing the deterministic stdout log."""
    print(f"  [detail] {message}", file=sys.stderr, flush=True)


def require(cond, msg):
    """hard gate for internal certificate identities: unlike `assert`,
    survives `python3 -O` and always aborts with a nonzero exit."""
    if not cond:
        raise RuntimeError(f"certificate identity failed: {msg}")


Dv, xv = sp.symbols('D x')
a, b, a2 = sp.symbols('a b a2')
M_, Q_ = sp.symbols('M Q')


def scaled_chain(u, lo, hi, seeds):
    """P[i], c[i] for lo <= i <= hi; k0 = (D-u)/2 symbolic; P poly in
    (D, x, seeds); c[i] poly in D (positive on sector)."""
    k0 = (Dv - u)/2
    P = dict(seeds)
    c = {lo: sp.Integer(1), lo+1: sp.Integer(1)}
    i = lo + 1
    while i < hi:
        # step producing P[i+1] from index j = k0+i
        c[i+1] = sp.expand(c[i]*(k0 + i + 1))
        ratio = sp.cancel(c[i]/c[i-1])
        P[i+1] = sp.expand(xv*P[i] + (k0 + i - 1 - Dv)*ratio*P[i-1])
        i += 1
    return P, c


def build_G(u, eps, version):
    if version == 1:
        P, c = scaled_chain(u, 0, u+2, {0: a, 1: b})
        v1, v2 = a, b
        con = sp.expand(P[u] - eps*c[u]*v1)      # lam*a + mu*b
    else:
        P, c = scaled_chain(u, -1, u+2, {-1: a2, 0: a})
        v1, v2 = a2, a
        con = sp.expand(P[u+1] - eps*c[u+1]*v1)
    lam = sp.expand(con.coeff(v1)); mu = sp.expand(con.coeff(v2))
    require(sp.expand(con - lam*v1 - mu*v2) == 0,
            "constraint decomposition con = lam*v1 + mu*v2")
    # Ttil = T * c[u+1] c[u+2]: polynomial quadratic form in (v1, v2)
    scale = {  # multiplier for each product, all polynomial:
        'uu':   sp.cancel(c[u+1]*c[u+2]/c[u]**2),
        'u_u2': sp.cancel(c[u+1]/c[u]),
        'u1u1': sp.cancel(c[u+2]/c[u+1]),
        'um_u1': sp.cancel(c[u+2]/c[u-1]),
    }
    for v in scale.values():
        den = sp.denom(sp.together(v))
        require(den.is_number and den > 0,
                "polynomial positive scale factor in Ttil")
    Ttil = sp.expand(scale['uu']*P[u]**2 + scale['u_u2']*P[u]*P[u+2]
                     - scale['u1u1']*P[u+1]**2
                     - scale['um_u1']*P[u-1]*P[u+1])
    A = sp.expand(sp.diff(Ttil, v1, 2)/2)
    C = sp.expand(sp.diff(Ttil, v2, 2)/2)
    B = sp.expand(sp.diff(sp.diff(Ttil, v1), v2))
    require(sp.expand(Ttil - A*v1**2 - B*v1*v2 - C*v2**2) == 0,
            "quadratic-form decomposition of Ttil")
    G = sp.expand(A*mu**2 - B*lam*mu + C*lam**2)
    # identities on the constraint line lam v1 + mu v2 = 0:
    #   Ttil*mu^2 == G*v1^2  (v2 = -lam v1 / mu)
    #   Ttil*lam^2 == G*v2^2 (v1 = -mu v2 / lam)
    lhs_mu = sp.expand(A*v1**2*mu**2 + B*v1*(-lam*v1)*mu + C*(lam*v1)**2)
    lhs_lam = sp.expand(A*(-mu*v2)**2 + B*(-mu*v2)*(lam*v2) + C*v2**2*lam**2)
    idok = (sp.expand(lhs_mu - G*v1**2) == 0
            and sp.expand(lhs_lam - G*v2**2) == 0)
    GMQ = sp.expand(G.subs({Dv: M_+Q_, xv: M_-Q_}))
    AMQ = sp.expand(A.subs({Dv: M_+Q_, xv: M_-Q_}))
    BMQ = sp.expand(B.subs({Dv: M_+Q_, xv: M_-Q_}))
    CMQ = sp.expand(C.subs({Dv: M_+Q_, xv: M_-Q_}))
    lamMQ = sp.expand(lam.subs({Dv: M_+Q_, xv: M_-Q_}))
    muMQ = sp.expand(mu.subs({Dv: M_+Q_, xv: M_-Q_}))
    return GMQ, idok, lamMQ, muMQ, AMQ, BMQ, CMQ


def cert_factor(f, tmax, Mmax=1145):
    pe = sp.Poly(f, M_, Q_)
    terms = [(m[0], m[1], F(cc.p, cc.q)) for m, cc in pe.terms()]
    d = max(am + bm for am, bm, _ in terms)
    Lc, S = {}, {}
    for am, bm, cc in terms:
        j = d - (am + bm)
        if j == 0:
            Lc[bm] = Lc.get(bm, F(0)) + cc
        else:
            S[j] = S.get(j, F(0)) + abs(cc)*tmax**bm
    n = 512
    dbound = sum(abs(cc)*bm*tmax**(bm-1) if bm else F(0)
                 for bm, cc in Lc.items())
    Lmin = min(sum(cc*(tmax*F(k, n))**bm for bm, cc in Lc.items())
               for k in range(n+1))
    Lmin_low = Lmin - dbound*tmax/(2*n)
    if Lmin_low <= 0:
        return False, None
    M0 = 2
    while sum(Sj*F(1, M0**j) for j, Sj in S.items()) >= Lmin_low:
        M0 *= 2
        if M0 > Mmax:
            return False, None
    lo, hi = M0//2, M0
    while lo + 1 < hi:
        mid = (lo+hi)//2
        if sum(Sj*F(1, mid**j) for j, Sj in S.items()) < Lmin_low:
            hi = mid
        else:
            lo = mid
    return True, hi


def cert_positive(G, tmax):
    """G >= 0 on the enlarged auxiliary sector
    {M >= max(221, M0), 3 <= Q <= tmax*M}, with every odd-multiplicity
    factor positive; return (ok, M0, note).  The manuscript only invokes
    this stronger certificate after its separately checked bound M >= 425.
    """
    const, facs = sp.factor_list(G)
    if const == 0:
        return False, None, "zero"
    sign = 1 if const > 0 else -1
    M0max, notes = 0, []
    for f, mult in facs:
        pf = sp.Poly(f, M_, Q_)
        if pf.total_degree() == 0:
            continue
        if mult % 2 == 0:
            notes.append(f"even^{mult}(deg{pf.total_degree()})")
            continue
        if pf.total_degree() == 1:
            am, bm, cm = pf.nth(1, 0), pf.nth(0, 1), pf.nth(0, 0)
            corners = [am*221 + bm*3 + cm, am*221 + bm*221*tmax + cm]
            if am >= 0 and am + bm*tmax >= 0 and all(v > 0 for v in corners):
                notes.append("lin+")
                continue
            if am <= 0 and am + bm*tmax <= 0 and all(v < 0 for v in corners):
                notes.append("lin-")
                if mult % 2: sign = -sign
                continue
            return False, None, f"linear unresolved: {f}"
        ok, M0 = cert_factor(f, tmax)
        if not ok:
            ok2, M0 = cert_factor(sp.expand(-f), tmax)
            if not ok2:
                return False, None, f"factor fails: deg {pf.total_degree()}"
            sign = -sign
        M0max = max(M0max, M0)
        notes.append(f"core{pf.total_degree()}(M0={M0})")
    if sign < 0:
        return False, None, "negative overall"
    return True, M0max, ",".join(notes)


def int_roots(poly_expr, var):
    """all integer roots via factor_list linear factors (exact)."""
    out = set()
    _, facs = sp.factor_list(poly_expr, var)
    for f, _m in facs:
        pf = sp.Poly(f, var)
        if pf.degree() == 1:
            r = sp.Rational(-pf.nth(0), pf.nth(1))
            if r.is_integer:
                out.add(int(r))
    return out


def no_root_prime(poly_expr, var):
    """Return a prime at which a nonlinear rational polynomial has no root.

    Such a prime is a compact, independently replayable witness that the
    factor has no integer root.  Denominators and the leading coefficient
    are required to remain nonzero modulo the selected prime.
    """
    poly = sp.Poly(poly_expr, var, domain=sp.QQ)
    require(poly.degree() >= 2, "no-root prime requested for nonlinear factor")
    coeffs = [sp.Rational(value) for value in poly.all_coeffs()]
    for prime in sp.primerange(2, 200000):
        if any(int(value.q) % prime == 0 for value in coeffs):
            continue
        modular = [int(value.p) * pow(int(value.q), -1, prime) % prime
                   for value in coeffs]
        if modular[0] == 0:
            continue
        has_root = False
        for residue in range(prime):
            value = 0
            for coefficient in modular:
                value = (value*residue + coefficient) % prime
            if value == 0:
                has_root = True
                break
        if not has_root:
            return int(prime)
    raise RuntimeError(f"no modular no-root witness found for {poly_expr}")


def export_factorization(witness, label, expr, variables, kind,
                         modular_root_witnesses=False):
    const, factors = sp.factor_list(expr)
    const = sp.Rational(const)
    witness.meta(f"{kind}_CONST", label, int(const.p), int(const.q))
    for index, (factor, multiplicity) in enumerate(factors):
        name = f"{label}_factor_{index}"
        witness.poly(name, factor, variables)
        prime = 0
        if modular_root_witnesses:
            univariate = sp.Poly(factor, *variables)
            if len(variables) == 1 and univariate.degree() >= 2:
                prime = no_root_prime(factor, variables[0])
        witness.meta(f"{kind}_FACTOR", label, name, multiplicity, prime)


def export_finite_case(witness, label, u, eps, version,
                       G, lam, mu, A, B, C,
                       Gr, lamr, mur, common, tmax, M0):
    names = {}
    for suffix, expression in (
            ("G", G), ("lam", lam), ("mu", mu),
            ("A", A), ("B", B), ("C", C),
            ("Gr", Gr), ("lamr", lamr), ("mur", mur),
            ("common", common)):
        name = f"{label}_{suffix}"
        witness.poly(name, expression, (M_, Q_))
        names[suffix] = name
    witness.meta("FINITE_CASE", label, u, eps, version,
                 names["G"], names["lam"], names["mu"],
                 names["A"], names["B"], names["C"],
                 names["Gr"], names["lamr"], names["mur"],
                 names["common"], tmax.numerator, tmax.denominator,
                 M0 or 0)
    export_factorization(witness, label, Gr, (M_, Q_), "FINITE_G")


def export_resultant(witness, label, f1, f2, resultant):
    names = []
    for suffix, expression in (("f", f1), ("h", f2), ("R", resultant)):
        name = f"{label}_{suffix}"
        variables = (M_, Q_) if suffix != "R" else (M_,)
        witness.poly(name, expression, variables)
        names.append(name)
    witness.meta("RESULTANT", label, names[0], names[1], names[2], 1145, 24)
    export_factorization(witness, label, resultant, (M_,), "RESULTANT",
                         modular_root_witnesses=True)


def no_common_sector_zeros(f1, f2, witness=None, label=None):
    """Certify that {f1 = f2 = 0} has no integer point with M > 1145
    in the deliberately enlarged sector 3 <= Q <= M/24.  This contains
    the manuscript sector Q < M/(u+1)^2 <= M/25.  Use a resultant in Q,
    integer M-candidates, and exact specialized gcd checks.
    """
    phase = label or "unlabelled-pair"
    progress_detail(
        f"{phase}: resultant start; "
        f"degrees_Q=({sp.degree(f1, Q_)},{sp.degree(f2, Q_)})")
    R = sp.resultant(f1, f2, Q_)
    progress_detail(
        f"{phase}: resultant complete; degree_M={sp.degree(R, M_)}")
    if R == 0:
        return False, "resultant zero (common factor)"
    if witness:
        require(label is not None, "resultant witness label is present")
        progress_detail(f"{phase}: witness factorization start")
        export_resultant(witness, label, f1, f2, R)
        progress_detail(f"{phase}: witness factorization complete")
    Rp = sp.Poly(R, M_)
    progress_detail(f"{phase}: integer-root census start")
    cands = int_roots(R, M_) if Rp.degree() > 0 else set()
    progress_detail(
        f"{phase}: integer-root census complete; candidates={len(cands)}")
    for Mc in cands:
        if Mc <= 1145:
            continue
        g = sp.gcd(sp.Poly(f1.subs(M_, Mc), Q_),
                   sp.Poly(f2.subs(M_, Mc), Q_))
        gp = sp.Poly(g, Q_)
        if gp.is_zero:
            # both specializations vanish identically: every Q is a
            # common zero at M = Mc, so this must FAIL, not fall
            # through the degree-0 test below.
            return False, f"specialized gcd identically zero at M={Mc}"
        if gp.degree() == 0:
            continue
        for r in int_roots(g.as_expr(), Q_):
            if 3 <= r and 24*r <= Mc:
                return False, f"common zero at (M,Q)=({Mc},{r})"
    return True, f"res deg {Rp.degree()}, {len(cands)} cands"


def reduce_version(GMQ, lam, mu):
    """strip gcd(lam, mu): identity divides through by g^2 wherever
    g != 0.  Returns (G', lam', mu', g)."""
    g = sp.gcd(lam, mu)
    if sp.Poly(g, M_, Q_).total_degree() == 0:
        return GMQ, lam, mu, sp.Integer(1)
    lam2 = sp.cancel(lam/g); mu2 = sp.cancel(mu/g)
    G2 = sp.cancel(GMQ/g**2)
    require(sp.denom(sp.together(G2)).is_number,
            "G/g^2 is a polynomial")
    G2 = sp.expand(G2)
    require(sp.expand(GMQ - g**2*G2) == 0, "exact identity G = g^2 G'")
    return G2, sp.expand(lam2), sp.expand(mu2), g


def pcoef(M, Q):
    D = M + Q
    p = [0]*(D+1)
    for i in range(M+1):
        for j in range(Q+1):
            p[i+j] += comb(M, i)*comb(Q, j)*(-1)**(Q-j)
    return p


def gap_cells_for_u(u, eps, want=2, dmax=None):
    """First `want` gap cells (D, Q) with Q >= 3 and (-1)^Q == eps at
    offset u, by exact integer scan (x descending through the admissible
    window per D).  dmax comfortably exceeds the first cells of both
    parities for u <= 14 (worst observed: D = 4932 at u=14, eps=+1)."""
    if dmax is None:
        dmax = max(1200, 45*(u+2)**2)
    out = []
    U = (u+1)**2
    for D in range(max(u, 4), dmax):
        if (D - u) % 2:
            continue
        E = (D+3)**2
        upper = (D+1)**2 - U
        if upper <= 0:
            continue
        x = isqrt(upper - 1)
        if (x - D) % 2:
            x -= 1
        while x >= 0 and x*x*U > (U-1)*(E-U):
            Q = (D - x)//2
            if Q >= 3 and (-1)**Q == eps:
                out.append((D, Q))
            x -= 2
        if len(out) >= want:
            return out[:want]
    return out


def first_open_gap(qmin, umax, dstart, dstop):
    """Return the first (D,Q,u) with Q >= qmin and u > umax.

    For fixed D, a gap is U < U_-, so the first parity-compatible u above
    umax decides whether any larger u can be a gap.  For this fixed (D,u),
    x = D-2Q runs through the nonnegative integers of parity D.  The two
    strict gap inequalities are

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


def numeric_spot(u, eps, GMQ, version):
    """verify T*c_{u+1}c_{u+2}*mu^2 == G*a^2 at real gap cells of the
    requested Q-parity; the tested cell count is returned and reported,
    and the caller requires it to be >= 1 (a vacuous run is a FAIL)."""
    cells = gap_cells_for_u(u, eps)
    okn = True
    for (D, Q) in cells:
        M = D - Q
        p = pcoef(M, Q)
        s = (D+u)//2; k0 = s - u
        T = p[s]**2 + p[s]*p[s+2] - p[s+1]**2 - p[s-1]*p[s+1]
        # rebuild scaled quantities numerically
        lo = 0 if version == 1 else -1
        c = {lo: 1, lo+1: 1}
        for i in range(lo+1, u+2):
            c[i+1] = c[i]*(k0 + i + 1)
        if version == 1:
            lam_mu_from = u; base = p[k0]; other = p[k0+1]
        else:
            lam_mu_from = u+1; base = p[k0-1]; other = p[k0]
        # constraint coefficients numerically: P[idx] = lam0*seed1 +
        # mu0*seed2 with actual values: use linearity via two chains
        def chainval(s1, s2):
            P = {lo: s1, lo+1: s2}
            for i in range(lo+1, u+2):
                P[i+1] = (M-Q)*P[i] + (k0+i-1-D)*(c[i]//c[i-1])*P[i-1]
            return P
        Pa = chainval(1, 0); Pb = chainval(0, 1)
        lam = Pa[lam_mu_from] - eps*c[lam_mu_from]
        mu = Pb[lam_mu_from]
        Gval = GMQ.subs({M_: M, Q_: Q})
        lhs = T*c[u+1]*c[u+2]*mu*mu
        rhs = Gval*base*base
        if lhs != rhs:
            okn = False
        # sanity: constraint holds
        if lam*base + mu*other != 0:
            okn = False
    return okn, len(cells)


def main():
    UMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    witness_path = os.environ.get("KRAW_EXPORT_WITNESS")
    witness = (WitnessWriter(witness_path, "finite-offset")
               if witness_path else None)

    print("== [S] sector estimate (per-u): gap(u), Q >= 3 => Q < M/(u+1)^2 ==")
    # (i) analytic step:
    # gap: (2Q+3)(2M+3) < U + E/U - 1, and U < U- <= sqrt(E) = D+3.
    # (2M+3) >= (D+3) [Q <= M] => 2Q+3 < (D+3)/U + U/(D+3) <= (D+3)/U + 1.
    # 2Q+3 >= 9 => (D+3)/U > 8 => U/(D+3) < 1/8.
    # 2Q+3 < W/U + 1/8 (W = 2M+3 >= D+3)
    # => Q < M/U + 3/(2U) - (3 - 1/8)/2 < M/U once 3/(2U) < 1.4375:
    check("3/(2U) < 1.4375 for U >= 25", F(3, 50) < F(23, 16))
    # (ii) exact in-script census (no external premise): no gap cell
    # with u >= 4, Q >= 3, D < 442.  By gap heredity (U- is u-free)
    # only the first parity-compatible u in {4, 5} need be tested per
    # (D, Q):
    first_hit = None
    for D in range(1, 442):
        E = (D+3)**2
        u0 = 4 if D % 2 == 0 else 5
        if u0 > D:
            continue
        U = (u0+1)**2
        for Q in range(3, D//2 + 1):
            x = D - 2*Q
            if U < (D+1)**2 - x*x and x*x*U > (U-1)*(E-U):
                first_hit = (D, Q, u0)
    check("census: no gap cell with u >= 4, Q >= 3, D < 442 "
          "(heredity-reduced exact scan)", first_hit is None)
    # hence on the sector M > D*25/26 >= 442*25/26 = 425 >= 221:
    check("442*25/26 >= 425 >= 221", F(442*25, 26) >= 425 >= 221)

    print(f"== [G] gap offsets u = 4..{UMAX} ==", flush=True)
    allM0 = 0
    for u in range(4, UMAX+1):
        row = []
        rowM0 = 0
        for eps in (1, -1):
            parity_name = "p" if eps == 1 else "m"
            print(f"  [progress] offset {u}/{UMAX}, parity {eps:+d}, "
                  "primary pinning", flush=True)
            # V1 reduced: covers all cells with g1 != 0
            progress_detail(f"u={u} eps={eps:+d} v1: recurrence build start")
            G1, id1, lam1, mu1, A1, B1, C1 = build_G(u, eps, 1)
            progress_detail(f"u={u} eps={eps:+d} v1: recurrence build complete")
            n1, ncells1 = numeric_spot(u, eps, G1, 1)
            G1r, lam1r, mu1r, g1 = reduce_version(G1, lam1, mu1)
            progress_detail(f"u={u} eps={eps:+d} v1: reduction complete")
            tmax = F(1, (u+1)**2)
            progress_detail(f"u={u} eps={eps:+d} v1: sector factor check start")
            ok1, M01, note1 = cert_positive(G1r, tmax)
            progress_detail(f"u={u} eps={eps:+d} v1: sector factor check complete")
            label1 = f"finite_u{u}_e{parity_name}_v1"
            cz1, czn1 = no_common_sector_zeros(
                lam1r, mu1r, witness, f"{label1}_reduced_pair")
            v1ok = id1 and n1 and ok1 and cz1 and ncells1 >= 1
            if not v1ok:
                print(f"    v1 fails u={u} eps={eps}: ident={id1} "
                      f"num={n1}({ncells1} cells) pos={ok1} ({note1}) "
                      f"czf={cz1} ({czn1})")
                row.append(False); continue
            rowM0 = max(rowM0, M01 or 0)
            if witness:
                export_finite_case(
                    witness, label1, u, eps, 1,
                    G1, lam1, mu1, A1, B1, C1,
                    G1r, lam1r, mu1r, g1, tmax, M01)
            print(f"    u={u} eps={eps:+d} v1: factors={note1}; "
                  f"M0={M01}; reduced-pair {czn1}; spot={ncells1}")
            if sp.Poly(g1, M_, Q_).total_degree() == 0:
                print("      primary common factor is constant; "
                      "no alternate pinning needed")
                row.append(True); continue
            # g1 nonconstant: cover {g1 = 0} cells by V2 reduced
            print(f"  [progress] offset {u}/{UMAX}, parity {eps:+d}, "
                  "alternate pinning", flush=True)
            progress_detail(f"u={u} eps={eps:+d} v2: recurrence build start")
            G2, id2, lam2, mu2, A2, B2, C2 = build_G(u, eps, 2)
            progress_detail(f"u={u} eps={eps:+d} v2: recurrence build complete")
            n2, ncells2 = numeric_spot(u, eps, G2, 2)
            G2r, lam2r, mu2r, g2 = reduce_version(G2, lam2, mu2)
            progress_detail(f"u={u} eps={eps:+d} v2: reduction complete")
            progress_detail(f"u={u} eps={eps:+d} v2: sector factor check start")
            ok2, M02, note2 = cert_positive(G2r, tmax)
            progress_detail(f"u={u} eps={eps:+d} v2: sector factor check complete")
            label2 = f"finite_u{u}_e{parity_name}_v2"
            cz2, czn2 = no_common_sector_zeros(
                lam2r, mu2r, witness, f"{label2}_reduced_pair")
            # v2 usable at g1=0 cells iff g2 != 0 there:
            cg, cgn = no_common_sector_zeros(
                g1, g2, witness, f"{label2}_common_factors")
            v2ok = id2 and n2 and ok2 and cz2 and cg and ncells2 >= 1
            if not v2ok:
                print(f"    v2 fails u={u} eps={eps}: ident={id2} "
                      f"num={n2}({ncells2} cells) pos={ok2} ({note2}) "
                      f"czf={cz2} ({czn2}) g1g2={cg} ({cgn})")
            else:
                if witness:
                    export_finite_case(
                        witness, label2, u, eps, 2,
                        G2, lam2, mu2, A2, B2, C2,
                        G2r, lam2r, mu2r, g2, tmax, M02)
                print(f"      v2: factors={note2}; M0={M02}; "
                      f"reduced-pair {czn2}; common-factors {cgn}; "
                      f"spot={ncells2}")
            rowM0 = max(rowM0, M02 or 0)
            row.append(v2ok)
        allM0 = max(allM0, rowM0)
        check(f"u={u}: both parities certified [maxM0={rowM0}]", all(row))
        if witness and all(row):
            witness.checkpoint(f"u{u}")

    check(f"max M0 = {allM0} <= 153 (manuscript table) "
          f"<= 1145 (scan covers the remainder)",
          allM0 <= 153 <= 1145)
    # The resultant-based nondegeneracy checker starts at M > 1145.
    # On the skipped sector, Q < M/(u+1)^2 <= M/25, so M <= 1145
    # implies the integer bound Q <= 45 and hence D <= 1190.
    check("nondegeneracy range M <= 1145 has D <= 1190 < 1200",
          1145 + 45 == 1190 and 1190 < 1200)

    print("== [T] threshold ==")
    # smallest D with a gap cell u > UMAX, Q >= 3 -- exact scan from D=4,
    # no external premise about small D
    threshold_witness = first_open_gap(3, UMAX, 4, 40000)
    print(f"  first open gap cell (u > {UMAX}, Q >= 3): {threshold_witness}")
    if threshold_witness is None:
        check("threshold census found a first open cell", False)
        thr = None
    else:
        thr = threshold_witness[0]
        if UMAX == 14:
            # the manuscript's census values are asserted, not just
            # printed:
            check(f"threshold census matches manuscript: {threshold_witness} == "
                  f"(4587, 3, 15); m* = {thr-1}",
                  threshold_witness == (4587, 3, 15))
        else:
            check(f"threshold census is nonempty; m* = {thr-1}", True)

    print("== FINITE GAP OFFSETS:", "ALL CHECKS PASS ==" if OK else "FAILURES ==")
    if OK and thr is not None:
        print(f"  => all offsets u <= {UMAX} are verified for every D,")
        print(f"     and every cell is verified for D <= {thr-1}")
        print(f"     (together with the regime, small-argument, and "
              f"D <= 1200 scan verifiers).")
        if witness:
            witness.meta("THRESHOLD", 3, UMAX,
                         threshold_witness[0], threshold_witness[1],
                         threshold_witness[2])
            witness.finish()
    raise SystemExit(0 if OK else 1)


if __name__ == '__main__':
    main()
