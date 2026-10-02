import Kraw.Defs

/-!
# Elementary facts about gap cells

Paper Lemma 3.5 (heredity of the gap) and Lemma 3.6 (gap strip), in the
square-root-free form used by the manuscript:  with `U = (u+1)^2`,
`E = (D+3)^2`, `h = E + 1 - x^2` and `q(t) = t^2 - h t + E`, a gap cell has
`q(U) > 0` and `U < U₀ := (D+1)^2 - x^2`, while `q(U₀) ≤ 0` for `0 ≤ x ≤ D`.
-/

namespace Kraw

private def gapQ (D x t : ℤ) : ℤ :=
  t ^ 2 - ((D + 3) ^ 2 + 1 - x ^ 2) * t + (D + 3) ^ 2

private theorem gapQ_eq_bulk (D x t : ℤ) :
    gapQ D x t = x ^ 2 * t - (t - 1) * ((D + 3) ^ 2 - t) := by
  unfold gapQ
  ring

private theorem gapQ_flow_nonpos {D x : ℤ} (hD : 0 ≤ D) (hx : 0 ≤ x)
    (hxD : x ≤ D) : gapQ D x ((D + 1) ^ 2 - x ^ 2) ≤ 0 := by
  have hxSq : x ^ 2 ≤ D ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hxD) (show 0 ≤ D + x by omega)
    nlinarith [hprod]
  have hbase : 0 ≤ 7 * D ^ 2 + 16 * D := by nlinarith
  have hbracket :
      0 ≤ (D ^ 2 + 2 * D - x ^ 2) * (4 * D + 8) - x ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hxSq) (show 0 ≤ 4 * D + 9 by omega)
    nlinarith [hprod, hbase]
  have hformula :
      gapQ D x ((D + 1) ^ 2 - x ^ 2) =
        -((D ^ 2 + 2 * D - x ^ 2) * (4 * D + 8) - x ^ 2) := by
    unfold gapQ
    ring
  rw [hformula]
  omega

private theorem gapQ_small {D x u : ℤ} (hg : Gap D x u) (hD : 0 ≤ D)
    (hx : 0 ≤ x) (hxD : x ≤ D) :
    2 * (u + 1) ^ 2 ≤ (D + 3) ^ 2 + 1 - x ^ 2 := by
  rcases hg with ⟨hu, hbulk, hflow⟩
  let U : ℤ := (u + 1) ^ 2
  let U₀ : ℤ := (D + 1) ^ 2 - x ^ 2
  have hqU : 0 < gapQ D x U := by
    rw [gapQ_eq_bulk]
    dsimp [U]
    linarith [hbulk]
  have hqU₀ : gapQ D x U₀ ≤ 0 := by
    dsimp [U₀]
    exact gapQ_flow_nonpos hD hx hxD
  by_contra hnot
  have hlarge : (D + 3) ^ 2 + 1 - x ^ 2 < 2 * U := by omega
  have hU₀U : U < U₀ := by
    dsimp [U, U₀] at hflow ⊢
    exact hflow
  have hsum : 0 < U₀ + U - ((D + 3) ^ 2 + 1 - x ^ 2) := by
    dsimp [U₀, U] at *
    nlinarith
  have hfactor : 0 < U₀ - U := sub_pos.mpr hU₀U
  have hdiff :
      gapQ D x U₀ - gapQ D x U =
        (U₀ - U) * (U₀ + U - ((D + 3) ^ 2 + 1 - x ^ 2)) := by
    unfold gapQ
    ring
  have hinc : gapQ D x U < gapQ D x U₀ := by
    have hmul := mul_pos hfactor hsum
    nlinarith [hdiff, hmul]
  have hqU₀pos : 0 < gapQ D x U₀ := lt_trans hqU hinc
  exact (not_lt_of_ge hqU₀) hqU₀pos

private theorem gapQ_between_nonpos {D x aDen aNum t b : ℤ}
    (hDen : 0 < aDen) (hleft : aNum ≤ aDen * t) (hright : aDen * t < aDen * b)
    (hqa : aNum ^ 2 - ((D + 3) ^ 2 + 1 - x ^ 2) * aNum * aDen +
      (D + 3) ^ 2 * aDen ^ 2 ≤ 0)
    (hqb : gapQ D x b ≤ 0) : gapQ D x t ≤ 0 := by
  have htB : t < b := by
    by_contra h
    have hbt : b ≤ t := le_of_not_gt h
    have hmul := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hDen)
      (sub_nonpos.mpr hbt)
    nlinarith [hright]
  have hleft' : 0 ≤ aDen * t - aNum := by omega
  have hright' : 0 < aDen * b - aNum := by
    have hmul := mul_pos hDen (sub_pos.mpr htB)
    nlinarith
  have hcoeff : 0 ≤ aDen * (aDen * t - aNum) :=
    mul_nonneg (le_of_lt hDen) hleft'
  have hterm₁ : (b - t) *
      (aNum ^ 2 - ((D + 3) ^ 2 + 1 - x ^ 2) * aNum * aDen +
        (D + 3) ^ 2 * aDen ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (le_of_lt htB)) hqa
  have hterm₂ : aDen * (aDen * t - aNum) * gapQ D x b ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoeff hqb
  have hprod : 0 ≤ (aDen * t - aNum) * (b - t) * (aDen * b - aNum) :=
    mul_nonneg (mul_nonneg hleft' (le_of_lt (sub_pos.mpr htB)))
      (le_of_lt hright')
  have hid :
      (b - t) * (aNum ^ 2 - ((D + 3) ^ 2 + 1 - x ^ 2) * aNum * aDen +
        (D + 3) ^ 2 * aDen ^ 2) +
      aDen * (aDen * t - aNum) * gapQ D x b -
        aDen * (aDen * b - aNum) * gapQ D x t =
      (aDen * t - aNum) * (b - t) * (aDen * b - aNum) := by
    unfold gapQ
    ring
  have hscaled : aDen * (aDen * b - aNum) * gapQ D x t ≤ 0 := by
    nlinarith [hid, hterm₁, hterm₂, hprod]
  have hpositive : 0 < aDen * (aDen * b - aNum) :=
    mul_pos hDen hright'
  by_contra h
  have htpos : 0 < gapQ D x t := by omega
  have hcontr := mul_pos hpositive htpos
  nlinarith

/-- A gap cell has `x ≠ 0`. -/
theorem gap_x_pos {D x u : ℤ} (hg : Gap D x u) (hD : 0 ≤ D) (hx : 0 ≤ x) : 0 < x := by
  rcases hg with ⟨hu, hbulk, hflow⟩
  by_contra hxpos
  have hx0 : x = 0 := by omega
  have hEbound : (D + 1) ^ 2 ≤ (D + 3) ^ 2 := by nlinarith
  have hE_lt_U : (D + 3) ^ 2 < (u + 1) ^ 2 := by
    by_contra h
    have hUE : (u + 1) ^ 2 ≤ (D + 3) ^ 2 := le_of_not_gt h
    have hfac := mul_nonneg (by omega : 0 ≤ u) (by omega : 0 ≤ u + 2)
    have hprod₁ : 0 ≤ (u + 1) ^ 2 - 1 := by nlinarith [hfac]
    have hprod := mul_nonneg hprod₁ (sub_nonneg.mpr hUE)
    simp [hx0] at hbulk
    nlinarith [hbulk]
  simp [hx0] at hflow
  omega

/-- Lemma 3.5 (heredity): smaller positive offsets of a gap cell are gap cells. -/
theorem gap_hered {D x u u' : ℤ} (hg : Gap D x u) (hD : 0 ≤ D) (hx : 0 ≤ x) (hxD : x ≤ D)
    (h1 : 1 ≤ u') (h2 : u' ≤ u) : Gap D x u' := by
  rcases hg with ⟨hu, hbulk, hflow⟩
  have hU'le : (u' + 1) ^ 2 ≤ (u + 1) ^ 2 := by
    have hprod := mul_nonneg (by omega : 0 ≤ u - u') (by omega : 0 ≤ u + u' + 2)
    nlinarith [hprod]
  have hsmall : 2 * (u + 1) ^ 2 ≤ (D + 3) ^ 2 + 1 - x ^ 2 :=
    gapQ_small ⟨hu, hbulk, hflow⟩ hD hx hxD
  have hqU : 0 < gapQ D x ((u + 1) ^ 2) := by
    rw [gapQ_eq_bulk]
    linarith [hbulk]
  have hqU' : gapQ D x ((u' + 1) ^ 2) > 0 := by
    have hdiff :
        gapQ D x ((u' + 1) ^ 2) - gapQ D x ((u + 1) ^ 2) =
          (((u' + 1) ^ 2) - (u + 1) ^ 2) *
            ((u' + 1) ^ 2 + (u + 1) ^ 2 - ((D + 3) ^ 2 + 1 - x ^ 2)) := by
      unfold gapQ
      ring
    have hfactor₁ : (((u' + 1) ^ 2) - (u + 1) ^ 2) ≤ 0 := by omega
    have hfactor₂ :
        ((u' + 1) ^ 2 + (u + 1) ^ 2 - ((D + 3) ^ 2 + 1 - x ^ 2)) ≤ 0 := by
      omega
    have hmul := mul_nonneg_of_nonpos_of_nonpos hfactor₁ hfactor₂
    linarith [hdiff]
  have hflow' : (u' + 1) ^ 2 < (D + 1) ^ 2 - x ^ 2 :=
    lt_of_le_of_lt hU'le hflow
  have hbulk' :
      ((u' + 1) ^ 2 - 1) * ((D + 3) ^ 2 - (u' + 1) ^ 2) <
        x ^ 2 * (u' + 1) ^ 2 := by
    rw [gapQ_eq_bulk] at hqU'
    linarith
  exact ⟨h1, hbulk', hflow'⟩

set_option maxHeartbeats 1000000
/-- Lemma 3.6 (gap strip): with `D = x + 2Q`, `Q ≥ 0`, `x ≥ 0`,
every gap cell satisfies `6(2Q+3)(u+1)^2 < 7(D+3)`. -/
theorem gap_strip {D x u Q : ℤ} (hg : Gap D x u) (hQ : 0 ≤ Q) (hx : 0 ≤ x)
    (hD : D = x + 2 * Q) : 6 * (2 * Q + 3) * (u + 1) ^ 2 < 7 * (D + 3) := by
  rcases hg with ⟨hu, hbulk, hflow⟩
  let U : ℤ := (u + 1) ^ 2
  let E : ℤ := (D + 3) ^ 2
  let h : ℤ := E + 1 - x ^ 2
  let U₀ : ℤ := (D + 1) ^ 2 - x ^ 2
  let A : ℤ := 6 * h
  let N : ℤ := 7 * E
  let M : ℤ := Q + x
  have hD₀ : 0 ≤ D := by rw [hD]; omega
  have hxD : x ≤ D := by rw [hD]; omega
  have hD3 : 0 < D + 3 := by omega
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hform : h = (2 * Q + 3) * (2 * M + 3) + 1 := by
    dsimp [h, E, M]
    rw [hD]
    ring
  have hgapmargin : h - 3 * (D + 3) = 4 * M * Q + 3 * M + 3 * Q + 1 := by
    dsimp [h, E, M]
    rw [hD]
    ring
  have hgapmarginpos : 0 < h - 3 * (D + 3) := by
    have hMQ := mul_nonneg (by omega : 0 ≤ M) hQ
    rw [hgapmargin]
    nlinarith
  have hsumpos : 0 < h + 3 * (D + 3) := by nlinarith
  have hsquare : 9 * E < h ^ 2 := by
    have hprod := mul_pos hgapmarginpos hsumpos
    have hid : h ^ 2 - 9 * E = (h - 3 * (D + 3)) * (h + 3 * (D + 3)) := by
      dsimp [h, E]
      ring
    nlinarith [hid]
  have hsmallE : 49 * E < 6 * h ^ 2 := by nlinarith [hsquare, hE]
  have hqU : 0 < gapQ D x U := by
    rw [gapQ_eq_bulk]
    dsimp [U]
    linarith [hbulk]
  have hqU₀ : gapQ D x U₀ ≤ 0 := by
    dsimp [U₀]
    exact gapQ_flow_nonpos hD₀ hx hxD
  have hA : 0 < A := by dsimp [A]; linarith
  have hAN : N ^ 2 - h * N * A + E * A ^ 2 ≤ 0 := by
    have hfactor : 0 ≤ E * (6 * h ^ 2 - 49 * E) :=
      mul_nonneg hE (by nlinarith [hsmallE])
    have hid : N ^ 2 - h * N * A + E * A ^ 2 = -E * (6 * h ^ 2 - 49 * E) := by
      dsimp [N, A]
      ring
    rw [hid]
    nlinarith
  have hUflow : U < U₀ := by
    dsimp [U, U₀] at hflow ⊢
    exact hflow
  have hbound : A * U < N := by
    by_contra hnot
    have hleft : N ≤ A * U := le_of_not_gt hnot
    have hright : A * U < A * U₀ := by
      have hmul := mul_pos hA (sub_pos.mpr hUflow)
      dsimp [A] at hmul ⊢
      nlinarith
    have hbetween : gapQ D x U ≤ 0 :=
      gapQ_between_nonpos hA hleft hright hAN hqU₀
    exact (not_lt_of_ge hbetween) hqU
  have hlowerfactor : (2 * Q + 3) * (D + 3) ≤ h := by
    have hMcmp : D + 3 ≤ 2 * M + 3 := by
      dsimp [M]
      rw [hD]
      omega
    have hmul := mul_le_mul_of_nonneg_left hMcmp (by omega : 0 ≤ 2 * Q + 3)
    rw [hform]
    nlinarith
  have hscaled :
      6 * (2 * Q + 3) * (D + 3) * U < 7 * (D + 3) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hlowerfactor (by positivity)
    dsimp [A, N] at hbound
    dsimp [U] at hmul ⊢
    nlinarith [hbound, hE]
  by_contra hnot
  have hbad : 7 * (D + 3) ≤ 6 * (2 * Q + 3) * (u + 1) ^ 2 := le_of_not_gt hnot
  have hmul := mul_le_mul_of_nonneg_left hbad (le_of_lt hD3)
  dsimp [U] at hscaled
  nlinarith [hscaled]

end Kraw
