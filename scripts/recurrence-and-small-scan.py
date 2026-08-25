#!/usr/bin/env python3
"""Exact recurrence check and exhaustive small-parameter scan.

For
    p_s = [w^s](1+w)^M(1-w)^Q,  D=M+Q,  x=M-Q,
the program checks
    (s+1)p_{s+1} = x p_s + (s-1-D)p_{s-1}
on M,Q <= 30 and checks the Turan step
    T_s = p_s^2 + p_s p_{s+2} - p_{s+1}^2 - p_{s-1}p_{s+1}
for every top-half index on M,Q <= 90.
"""
from math import comb


def coefficients(M, Q):
    D = M + Q
    p = [0] * (D + 3)
    for a in range(M + 1):
        ca = comb(M, a)
        for b in range(Q + 1):
            p[a + b] += ca * comb(Q, b) * (-1) ** b
    return p


def turan_step(p, s):
    pm1 = p[s - 1] if s else 0
    return p[s] ** 2 + p[s] * p[s + 2] - p[s + 1] ** 2 - pm1 * p[s + 1]


def main():
    recurrence_ok = True
    for M in range(31):
        for Q in range(31):
            D = M + Q
            x = M - Q
            p = coefficients(M, Q)
            for s in range(D + 1):
                pm1 = p[s - 1] if s else 0
                recurrence_ok &= (
                    (s + 1) * p[s + 1]
                    == x * p[s] + (s - 1 - D) * pm1
                )
    print(f"  [{'PASS' if recurrence_ok else 'FAIL'}] coefficient recurrence, M,Q <= 30")

    positivity_ok = True
    cells = 0
    for M in range(91):
        for Q in range(91):
            D = M + Q
            p = coefficients(M, Q)
            for s in range((D + 1) // 2, D + 1):
                cells += 1
                positivity_ok &= turan_step(p, s) >= 0
    print(f"  [{'PASS' if positivity_ok else 'FAIL'}] T_s >= 0 on {cells} top-half cells, M,Q <= 90")

    ok = recurrence_ok and positivity_ok
    print("== RECURRENCE AND SMALL SCAN:", "ALL CHECKS PASS ==" if ok else "FAILURES ==")
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
