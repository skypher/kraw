import Mathlib

/-!
# Definitions

Paper: `paper/krawtchouk_turan_positivity.tex`, equations (1.1) and (1.2).

For integers `M Q ≥ 0`, `p M Q s = [w^s] (1+w)^M (1-w)^Q`, extended by zero to
negative indices.  `Tur` is the Turán determinant and `T` the Turán step.
Coordinates used throughout: `D = M + Q`, `x = M - Q`, `u = 2s - D`,
`U = (u+1)^2`, `E = (D+3)^2`.
-/

open Polynomial

namespace Kraw

/-- The generating polynomial `(1+w)^M (1-w)^Q`. -/
noncomputable def gen (M Q : ℕ) : ℤ[X] := (1 + X) ^ M * (1 - X) ^ Q

/-- `p M Q s = [w^s] (1+w)^M (1-w)^Q`, and `0` for `s < 0`. -/
noncomputable def p (M Q : ℕ) (s : ℤ) : ℤ :=
  if s < 0 then 0 else (gen M Q).coeff s.toNat

/-- The Turán determinant `p_s^2 - p_{s-1} p_{s+1}`. -/
noncomputable def Tur (M Q : ℕ) (s : ℤ) : ℤ :=
  p M Q s ^ 2 - p M Q (s - 1) * p M Q (s + 1)

/-- The Turán step `Tur(s) - Tur(s+1)`. -/
noncomputable def T (M Q : ℕ) (s : ℤ) : ℤ :=
  Tur M Q s - Tur M Q (s + 1)

/-- Gap cells (paper (3.8)) in the coordinates `D`, `x`, `u`:
`u ≥ 1`, failure of the bulk inequality `x^2 U ≤ (U-1)(E-U)`, and failure of the
flow inequality `U ≥ (D+1)^2 - x^2`, where `U = (u+1)^2`, `E = (D+3)^2`. -/
def Gap (D x u : ℤ) : Prop :=
  1 ≤ u ∧
    ((u + 1) ^ 2 - 1) * ((D + 3) ^ 2 - (u + 1) ^ 2) < x ^ 2 * (u + 1) ^ 2 ∧
    (u + 1) ^ 2 < (D + 1) ^ 2 - x ^ 2

end Kraw
