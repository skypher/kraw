# Review checklist

Each program prints one `[PASS]`/`[FAIL]` line per obligation, ends with an
`ALL CHECKS PASS` or `FAILURES` summary, and exits nonzero on any failure.
Its acceptance predicate is the conjunction of all printed checks.  In
`odd-minimum-gap.py`, hard internal invariants (exact division in the
recurrence, even powers in the `X = x^2` reduction) raise an exception that
is not removed by `python3 -O`.

## `scripts/regime-decomposition.py`

1. `[A]` quadratic-form identity (3.1): the recurrence eliminates `p_{s+2}`
   and `p_{s-1}`; symbolic equality and a grid check.
2. `[B]` reflection on a grid and the central identities (3.4).
3. `[C]` discriminant identity (3.2); bulk cells on a grid.
4. `[D]` the flow proof items (a)–(e) of Theorem 3.3, the link identities
   for `I_1`, `I_2`, and the exact conjugacy `r_s = k/y_s` on flow cells.
5. `[E]` the coverage margin `-q(U_0)`; every cell with `M, Q <= 45` is
   assigned to a mechanism and has `T_s >= 0`.
6. `[F]` Proposition 5.1; the gap-lemma identities used in Corollary 3.4 and
   Lemmas 3.5–3.6; gap strip and heredity on every gap cell with `D <= 300`.
7. `[G]` the real-argument counterexample `T_2 = -1430/117649`.

## `scripts/even-minimum-gap.py`

1. `[A]` identities (I1)–(I4) of Theorem 4.1: Turán-step identity, the
   quadratic form for `Tur(j)`, the `(p,d)` system, the comparison map, and
   the tangent addition and half-angle formulas.
2. `[B]` anchors for `D` even (`d_c = 0`) and `D` odd.
3. `[C]` the budget `(u+1)^2 sin^2 θ* < 7/3` (positive-coefficient
   numerator) and the closing cases `u = 1` (`7/12 < 3/4`), `u = 2`
   (`7/27 < 1/2`), `u >= 3` (`(u+2)/(u+1) <= 5/4`, `175/192 < 1`).
4. `[D]` exact orbit walks: `p` keeps its sign, `0 <= ζ_j <= t·Λ < x` with
   the tangent bound carried as an exact rational multiple of `√Λ`, and the
   decomposition (4.1) is termwise nonnegative.

## `scripts/odd-minimum-gap.py`

1. `[Y]`, `[W]`, `[A]`: the Möbius map, the window identity (5.1) and its
   discriminant, and the two anchors.
2. `[B]` the even-`D` base reduction to `x^2 <= (D+4)^2`; the odd-`D` base
   reduction to `B_o >= g_1` and the factorization
   `(D+3)^2(B_o^2-g_1^2) = 4(D+1)(D+5)((D+3)^2-(x-1)^2)`.
3. `[C1]` positivity of `K` and the boundary value
   `4(D+3)(u+2)(D+u+4)`.
4. `[S1]` the cleared transition identity (5.3), the decomposition into
   `P_1`, `R_1`, the concavity/monotonicity coefficients, `D > u` on the
   region, and `O_1`–`O_4` coefficient-nonnegative after
   `D = (30/7)(u+3)^2 - 3 + v`, `u = w + 1`.
5. `[R]` the region arithmetic in the proof of Theorem 5.3.
6. `[E]` exact window walks: `(p_j, p_{j+1})` lies in `C_{2j-D}` along the
   whole path and `T_s >= 0`, for every odd-`Q` gap cell with `u >= 2` and
   `D <= 600`.

## `scripts/recurrence-and-small-scan.py`

A cross-check only: the recurrence for `M,Q <= 30` against the binomial
definition and `T_s >= 0` for `M,Q <= 90`.
