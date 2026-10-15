# Certificate map

This file maps each statement of the manuscript (Version 2.0.3) whose
identities or signs are replayed by computer to its program and committed
log.  All checks use exact integer or rational arithmetic (SymPy); the
programs trust SymPy's polynomial expansion, cancellation, and
simplification.

| Manuscript result | Program | Log | Obligations |
|---|---|---|---|
| Recurrence (2.1) (cross-check) | `scripts/recurrence-and-small-scan.py` | `recurrence-and-small-scan.txt` | Recurrence against the binomial definition for `M,Q <= 30`; `T_s >= 0` directly for `M,Q <= 90`. Not used in the proof. |
| Theorems 3.1–3.3, Corollary 3.4, Lemmas 3.5–3.6, Proposition 5.1 | `scripts/regime-decomposition.py` | `regime-decomposition.txt` | Quadratic-form and discriminant identities; reflection and central identities; Riccati comparison algebra including the `I_1`/`I_2` link identities; exact flow conjugacy on a grid; `x^2U-(U-1)(E-U)=q(U)` and the value of `q(U_0)`; the identities for `h`, `h-3(D+3)`, `h-(2Q+3)(D+3)` and `q(7E/(6h))`; the odd `u = 1` closed form; gap strip and heredity on every gap cell with `D <= 300`; the real-argument example of §1.1. |
| Theorem 4.1 | `scripts/even-minimum-gap.py` | `even-minimum-gap.txt` | Turán-step identity (4.1); the `(p,d)` system; the comparison map and tangent addition; anchors for both parities of `D`; the angular budget `(u+1)^2 sin^2 θ* < 7/3` and the three closing cases `u = 1`, `u = 2`, `u >= 3`; exact orbit walks on every even-`Q` gap cell with `D <= 400`. |
| Lemma 5.2, Theorem 5.3 | `scripts/odd-minimum-gap.py` | `odd-minimum-gap.txt` | The Möbius map and window identity (5.1); anchors; both base inequalities (the odd-`D` base by the factorization `(D+3)^2(B_o^2-g_1^2) = 4(D+1)(D+5)((D+3)^2-(x-1)^2)`); the cleared transition identity (5.3); concavity of `P_1` and monotonicity of `R_1` and `K^2 - disc_2`; the boundary value of `Kx(u+1) - B_0C_0`; `O_1`–`O_4` coefficient-nonnegative after `D = (30/7)(u+3)^2 - 3 + v`, `u = w + 1`; the region arithmetic of Theorem 5.3; exact window walks on every odd-`Q` gap cell with `u >= 2` and `D <= 600`. |

The Lean 4 formalization in `lean/` proves every numbered statement and
displayed claim of the paper, including Proposition 1.3 (dual Jacobi–Trudi for
two columns and the irreducible `GL_D(ℂ)` character) and the coefficient table
of Lemma 5.2;
`lean/Kraw/Paper.lean` indexes them by number.  `make lean` builds it and
checks that all 77 indexed declarations use only the standard axioms;
`lean/ROADMAP.md` maps each Lean file to the paper.
