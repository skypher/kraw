import Mathlib

/-! Turán determinant and Turán step of an arbitrary real sequence (paper §1.1, §1.3). -/

namespace Kraw

/-- `f_s² - f_{s-1} f_{s+1}`. -/
def turSeq (f : ℤ → ℝ) (s : ℤ) : ℝ := f s ^ 2 - f (s - 1) * f (s + 1)

/-- `turSeq f s - turSeq f (s+1)`. -/
def stepSeq (f : ℤ → ℝ) (s : ℤ) : ℝ := turSeq f s - turSeq f (s + 1)

end Kraw
