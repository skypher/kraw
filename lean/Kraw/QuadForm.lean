import Kraw.Basic

/-!
# Quadratic form, bulk band, center, top cell

Paper Theorem 3.1 (quadratic-form identity and bulk band), Theorem 3.2 (center).
-/

namespace Kraw

variable (M Q : ℕ)

/-- Theorem 3.1, cleared form of (3.1): with `D = M+Q`, `x = M-Q`, `u = 2s-D`,
`(s+2)(D+1-s) T_s = (u+2)(D+1-s) p_s^2 - x(u+1) p_s p_{s+1} + u(s+2) p_{s+1}^2`.
Valid for every integer `s`. -/
theorem qform (s : ℤ) :
    (s + 2) * ((M : ℤ) + Q + 1 - s) * T M Q s =
      (2 * s - ((M : ℤ) + Q) + 2) * ((M : ℤ) + Q + 1 - s) * p M Q s ^ 2
      - ((M : ℤ) - Q) * (2 * s - ((M : ℤ) + Q) + 1) * p M Q s * p M Q (s + 1)
      + (2 * s - ((M : ℤ) + Q)) * (s + 2) * p M Q (s + 1) ^ 2 := by
  have h1 := p_rec M Q s
  have h2 := p_rec M Q (s + 1)
  have e : s + 1 - 1 = s := by ring
  rw [e] at h2
  unfold T Tur
  rw [e]
  -- eliminate `p_{s+2}` by (2.1) at `s+1` and `p_{s-1}` by (2.1) at `s`
  linear_combination ((M : ℤ) + Q + 1 - s) * p M Q s * h2
    - (s + 2) * p M Q (s + 1) * h1

/-- Theorem 3.1, bulk band (3.3): for `u ≥ 1`, `x^2 U ≤ (U-1)(E-U)` forces `T_s ≥ 0`. -/
theorem T_nonneg_bulk {s : ℤ} (hu : 1 ≤ 2 * s - ((M : ℤ) + Q)) (hs : s ≤ (M : ℤ) + Q)
    (hb : ((M : ℤ) - Q) ^ 2 * (2 * s - ((M : ℤ) + Q) + 1) ^ 2 ≤
      ((2 * s - ((M : ℤ) + Q) + 1) ^ 2 - 1) *
        (((M : ℤ) + Q + 3) ^ 2 - (2 * s - ((M : ℤ) + Q) + 1) ^ 2)) :
    0 ≤ T M Q s := by
  have hq := qform M Q s
  have hQ0 : (0 : ℤ) ≤ Q := Int.natCast_nonneg Q
  have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  have hs2 : 0 < s + 2 := by omega
  have hk : 0 < (M : ℤ) + Q + 1 - s := by omega
  have hA : 0 < (2 * s - ((M : ℤ) + Q) + 2) * ((M : ℤ) + Q + 1 - s) :=
    mul_pos (by omega) hk
  -- 4AC - B^2 equals the bulk margin, by 4(s+2)(D+1-s) = (D+3)^2 - (u+1)^2
  have hdisc : 0 ≤ 4 * ((2 * s - ((M : ℤ) + Q) + 2) * ((M : ℤ) + Q + 1 - s)) *
      ((2 * s - ((M : ℤ) + Q)) * (s + 2)) -
      ((M : ℤ) - Q) ^ 2 * (2 * s - ((M : ℤ) + Q) + 1) ^ 2 := by
    have e : 4 * ((2 * s - ((M : ℤ) + Q) + 2) * ((M : ℤ) + Q + 1 - s)) *
        ((2 * s - ((M : ℤ) + Q)) * (s + 2)) =
        ((2 * s - ((M : ℤ) + Q) + 1) ^ 2 - 1) *
          (((M : ℤ) + Q + 3) ^ 2 - (2 * s - ((M : ℤ) + Q) + 1) ^ 2) := by ring
    rw [e]; linarith
  -- completing the square: 4A·form = (2A a + B b)^2 + (4AC - B^2) b^2
  have hform : 0 ≤ (2 * s - ((M : ℤ) + Q) + 2) * ((M : ℤ) + Q + 1 - s) * p M Q s ^ 2
      - ((M : ℤ) - Q) * (2 * s - ((M : ℤ) + Q) + 1) * p M Q s * p M Q (s + 1)
      + (2 * s - ((M : ℤ) + Q)) * (s + 2) * p M Q (s + 1) ^ 2 := by
    have key : 4 * ((2 * s - ((M : ℤ) + Q) + 2) * ((M : ℤ) + Q + 1 - s)) *
        ((2 * s - ((M : ℤ) + Q) + 2) * ((M : ℤ) + Q + 1 - s) * p M Q s ^ 2
          - ((M : ℤ) - Q) * (2 * s - ((M : ℤ) + Q) + 1) * p M Q s * p M Q (s + 1)
          + (2 * s - ((M : ℤ) + Q)) * (s + 2) * p M Q (s + 1) ^ 2) =
        (2 * ((2 * s - ((M : ℤ) + Q) + 2) * ((M : ℤ) + Q + 1 - s)) * p M Q s
          - ((M : ℤ) - Q) * (2 * s - ((M : ℤ) + Q) + 1) * p M Q (s + 1)) ^ 2 +
        (4 * ((2 * s - ((M : ℤ) + Q) + 2) * ((M : ℤ) + Q + 1 - s)) *
          ((2 * s - ((M : ℤ) + Q)) * (s + 2)) -
          ((M : ℤ) - Q) ^ 2 * (2 * s - ((M : ℤ) + Q) + 1) ^ 2) * p M Q (s + 1) ^ 2 := by
      ring
    have hrhs : 0 ≤ (2 * ((2 * s - ((M : ℤ) + Q) + 2) * ((M : ℤ) + Q + 1 - s)) * p M Q s
          - ((M : ℤ) - Q) * (2 * s - ((M : ℤ) + Q) + 1) * p M Q (s + 1)) ^ 2 +
        (4 * ((2 * s - ((M : ℤ) + Q) + 2) * ((M : ℤ) + Q + 1 - s)) *
          ((2 * s - ((M : ℤ) + Q)) * (s + 2)) -
          ((M : ℤ) - Q) ^ 2 * (2 * s - ((M : ℤ) + Q) + 1) ^ 2) * p M Q (s + 1) ^ 2 :=
      add_nonneg (sq_nonneg _) (mul_nonneg hdisc (sq_nonneg _))
    rw [← key] at hrhs
    exact nonneg_of_mul_nonneg_right hrhs (by linarith)
  rw [← hq] at hform
  exact nonneg_of_mul_nonneg_right hform (mul_pos hs2 hk)

/-- Theorem 3.2 (center `u = 0`). -/
theorem T_center {s : ℤ} (hs : 2 * s = (M : ℤ) + Q) : 0 ≤ T M Q s := by
  have hQ0 : (0 : ℤ) ≤ Q := Int.natCast_nonneg Q
  have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  have r0 := p_refl M Q s
  have r1 := p_refl M Q (s + 1)
  have e0 : (M : ℤ) + Q - s = s := by omega
  have e1 : (M : ℤ) + Q - (s + 1) = s - 1 := by omega
  rw [e0] at r0
  rw [e1] at r1
  rcases Nat.even_or_odd Q with hQ | hQ
  · -- Q even: p_{s-1} = p_{s+1} and (D+2) p_{s+1} = x p_s
    rw [hQ.neg_one_pow, one_mul] at r1
    have hrec := p_rec M Q s
    rw [r1] at hrec
    have hrank : ((M : ℤ) + Q + 2) * p M Q (s + 1) = ((M : ℤ) - Q) * p M Q s := by
      linarith
    have hq := qform M Q s
    have hu0 : 2 * s - ((M : ℤ) + Q) = 0 := by omega
    rw [hu0] at hq
    have hs0 : 0 ≤ s := by omega
    -- (D+2)(s+2)(D+1-s) T = ((D+2)^2 - x^2) p_s^2
    have key : ((M : ℤ) + Q + 2) * ((s + 2) * ((M : ℤ) + Q + 1 - s) * T M Q s) =
        (((M : ℤ) + Q + 2) ^ 2 - ((M : ℤ) - Q) ^ 2) * p M Q s ^ 2 := by
      rw [hq]
      have e2 : (M : ℤ) + Q + 1 - s = s + 1 := by omega
      rw [e2]
      linear_combination (-((M : ℤ) - Q) * p M Q s) * hrank
        + (((M : ℤ) + Q + 2) * p M Q s ^ 2) * hs
    have hfac : 0 ≤ ((M : ℤ) + Q + 2) ^ 2 - ((M : ℤ) - Q) ^ 2 := by nlinarith
    have hrhs : 0 ≤ (((M : ℤ) + Q + 2) ^ 2 - ((M : ℤ) - Q) ^ 2) * p M Q s ^ 2 :=
      mul_nonneg hfac (sq_nonneg _)
    rw [← key] at hrhs
    have hpos : 0 < ((M : ℤ) + Q + 2) * ((s + 2) * ((M : ℤ) + Q + 1 - s)) :=
      mul_pos (by omega) (mul_pos (by omega) (by omega))
    rw [← mul_assoc] at hrhs
    exact nonneg_of_mul_nonneg_right hrhs hpos
  · -- Q odd: p_s = 0 and p_{s-1} = -p_{s+1}, so T_s = 0
    rw [hQ.neg_one_pow] at r0 r1
    have hps : p M Q s = 0 := by linarith
    have hT : T M Q s = 0 := by
      unfold T Tur
      have e : s + 1 - 1 = s := by ring
      rw [e, hps, r1]
      ring
    rw [hT]

/-- The top cell: `T_D = 1`. -/
theorem T_top : T M Q ((M : ℤ) + Q) = 1 := by
  unfold T Tur
  have h1 : p M Q ((M : ℤ) + Q + 1) = 0 := p_of_gt M Q (by omega)
  have h2 : p M Q ((M : ℤ) + Q + 1 + 1) = 0 := p_of_gt M Q (by omega)
  have e : (M : ℤ) + Q + 1 - 1 = (M : ℤ) + Q := by ring
  rw [h1, h2, e, p_top]
  have hsq : ((-1 : ℤ) ^ Q) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [hsq]
  ring

end Kraw
