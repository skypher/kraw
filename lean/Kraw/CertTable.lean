import Kraw.CertTableAux
import Mathlib

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-!
# Paper §7: the coefficient table for the transition certificates of Lemma 5.2

`P₁`, `R₁` are defined by the identity in the proof of Lemma 5.2; `O₁, …, O₄` are the
endpoint obligations.
-/

namespace Kraw

/-- `P₁(D,u,X)` from the proof of Lemma 5.2 (polynomial in `X = x²`). -/
noncomputable def cP1 (D u X : ℝ) : ℝ :=
  (-1 : ℝ) * D ^ 6 * u ^ 2 + (-2 : ℝ) * D ^ 6 * u + (-2 : ℝ) * D ^ 5 * u ^ 3 + (-24 : ℝ) * D ^ 5 * u ^ 2 + (-40 : ℝ) * D ^ 5 * u + (-26 : ℝ) * D ^ 4 * u ^ 3 + (3 : ℝ) * D ^ 4 * u ^ 2 * X + (-208 : ℝ) * D ^ 4 * u ^ 2 + (6 : ℝ) * D ^ 4 * u * X + (-312 : ℝ) * D ^ 4 * u + (2 : ℝ) * D ^ 4 * X + (2 : ℝ) * D ^ 3 * u ^ 5 + (18 : ℝ) * D ^ 3 * u ^ 4 + (2 : ℝ) * D ^ 3 * u ^ 3 * X + (-72 : ℝ) * D ^ 3 * u ^ 3 + (42 : ℝ) * D ^ 3 * u ^ 2 * X + (-792 : ℝ) * D ^ 3 * u ^ 2 + (80 : ℝ) * D ^ 3 * u * X + (-1184 : ℝ) * D ^ 3 * u + (28 : ℝ) * D ^ 3 * X + D ^ 2 * u ^ 6 + (28 : ℝ) * D ^ 2 * u ^ 5 + (-4 : ℝ) * D ^ 2 * u ^ 4 * X + (200 : ℝ) * D ^ 2 * u ^ 4 + (-10 : ℝ) * D ^ 2 * u ^ 3 * X + (280 : ℝ) * D ^ 2 * u ^ 3 + (-2 : ℝ) * D ^ 2 * u ^ 2 * X ^ 2 + (148 : ℝ) * D ^ 2 * u ^ 2 * X + (-1120 : ℝ) * D ^ 2 * u ^ 2 + (-4 : ℝ) * D ^ 2 * u * X ^ 2 + (332 : ℝ) * D ^ 2 * u * X + (-2176 : ℝ) * D ^ 2 * u + (-2 : ℝ) * D ^ 2 * X ^ 2 + (128 : ℝ) * D ^ 2 * X + (6 : ℝ) * D * u ^ 6 + (-2 : ℝ) * D * u ^ 5 * X + (112 : ℝ) * D * u ^ 5 + (-42 : ℝ) * D * u ^ 4 * X + (696 : ℝ) * D * u ^ 4 + (-176 : ℝ) * D * u ^ 3 * X + (1568 : ℝ) * D * u ^ 3 + (-12 : ℝ) * D * u ^ 2 * X ^ 2 + (-28 : ℝ) * D * u ^ 2 * X + (384 : ℝ) * D * u ^ 2 + (-24 : ℝ) * D * u * X ^ 2 + (384 : ℝ) * D * u * X + (-1536 : ℝ) * D * u + (-12 : ℝ) * D * X ^ 2 + (192 : ℝ) * D * X + u ^ 6 * X + (8 : ℝ) * u ^ 6 + (4 : ℝ) * u ^ 5 * X + (128 : ℝ) * u ^ 5 + (2 : ℝ) * u ^ 4 * X ^ 2 + (-54 : ℝ) * u ^ 4 * X + (736 : ℝ) * u ^ 4 + (16 : ℝ) * u ^ 3 * X ^ 2 + (-332 : ℝ) * u ^ 3 * X + (1792 : ℝ) * u ^ 3 + (26 : ℝ) * u ^ 2 * X ^ 2 + (-512 : ℝ) * u ^ 2 * X + (1536 : ℝ) * u ^ 2 + (12 : ℝ) * u * X ^ 2 + (-192 : ℝ) * u * X

/-- `R₁(D,u,X)` from the proof of Lemma 5.2. -/
noncomputable def cR1 (D u X : ℝ) : ℝ :=
  (2 : ℝ) * D ^ 4 * u + (2 : ℝ) * D ^ 4 + (2 : ℝ) * D ^ 3 * u ^ 2 + (28 : ℝ) * D ^ 3 * u + (28 : ℝ) * D ^ 3 + (-2 : ℝ) * D ^ 2 * u ^ 3 + (4 : ℝ) * D ^ 2 * u ^ 2 + (-2 : ℝ) * D ^ 2 * u * X + (116 : ℝ) * D ^ 2 * u + (-2 : ℝ) * D ^ 2 * X + (128 : ℝ) * D ^ 2 + (-2 : ℝ) * D * u ^ 4 + (-28 : ℝ) * D * u ^ 3 + (-76 : ℝ) * D * u ^ 2 + (-12 : ℝ) * D * u * X + (96 : ℝ) * D * u + (-12 : ℝ) * D * X + (192 : ℝ) * D + (-6 : ℝ) * u ^ 4 + (2 : ℝ) * u ^ 3 * X + (-68 : ℝ) * u ^ 3 + (14 : ℝ) * u ^ 2 * X + (-224 : ℝ) * u ^ 2 + (12 : ℝ) * u * X + (-192 : ℝ) * u

/-- `(D+u+4)² (K² - disc₂)/(u+2)` as a polynomial in `(D, u, X)`. -/
noncomputable def cO4X (D u X : ℝ) : ℝ :=
  D ^ 4 * u + (4 : ℝ) * D ^ 4 + (2 : ℝ) * D ^ 3 * u ^ 2 + (22 : ℝ) * D ^ 3 * u + (56 : ℝ) * D ^ 3 + (14 : ℝ) * D ^ 2 * u ^ 2 + (120 : ℝ) * D ^ 2 * u + (-4 : ℝ) * D ^ 2 * X + (256 : ℝ) * D ^ 2 + (-2 : ℝ) * D * u ^ 4 + (-22 : ℝ) * D * u ^ 3 + (-56 : ℝ) * D * u ^ 2 + (96 : ℝ) * D * u + (-24 : ℝ) * D * X + (384 : ℝ) * D + (-1 : ℝ) * u ^ 5 + (-18 : ℝ) * u ^ 4 + (-120 : ℝ) * u ^ 3 + (4 : ℝ) * u ^ 2 * X + (-352 : ℝ) * u ^ 2 + (24 : ℝ) * u * X + (-384 : ℝ) * u

/-- The defining identity of `P₁, R₁` (proof of Lemma 5.2): with `g² = disc₁`,
`(D+u+4)²[(K W₁ - B₀C₀)² - disc₂ W₁²] = 4(u+2)(P₁ + x R₁ g)`. -/
theorem cP1_cR1_spec (D u x g : ℝ) (hden : D + u + 4 ≠ 0)
    (hg : g ^ 2 = x ^ 2 * (u + 1) ^ 2 - u * (u + 2) * ((D + 3) ^ 2 - (u + 1) ^ 2)) :
    (D + u + 4) ^ 2 *
        ((x * ((u + 1) * D + u ^ 2 + 9 * u + 12) / (D + u + 4) * (x * (u + 1) + g) -
            u * (D - u) * ((u + 2) * (D + u + 6))) ^ 2 -
          (x ^ 2 * (u + 3) ^ 2 - (u + 2) * (u + 4) * ((D + 3) ^ 2 - (u + 3) ^ 2)) *
            (x * (u + 1) + g) ^ 2) =
      4 * (u + 2) * (cP1 D u (x ^ 2) + x * cR1 D u (x ^ 2) * g) := by
  unfold cP1 cR1
  field_simp [hden]
  linear_combination
    (x ^ 2 * ((u + 1) * D + u ^ 2 + 9 * u + 12) ^ 2 -
      (D + u + 4) ^ 2 *
        (x ^ 2 * (u + 3) ^ 2 -
          (u + 2) * (u + 4) * ((D + 3) ^ 2 - (u + 3) ^ 2))) * hg

/-- `(D+u+4)² (K² - disc₂)/(u+2) = cO4X D u (x²)`. -/
theorem cO4X_spec (D u x : ℝ) (hden : D + u + 4 ≠ 0) (hu : u + 2 ≠ 0) :
    (D + u + 4) ^ 2 *
        ((x * ((u + 1) * D + u ^ 2 + 9 * u + 12) / (D + u + 4)) ^ 2 -
          (x ^ 2 * (u + 3) ^ 2 - (u + 2) * (u + 4) * ((D + 3) ^ 2 - (u + 3) ^ 2))) / (u + 2) =
    cO4X D u (x ^ 2) := by
  unfold cO4X
  field_simp [hden, hu]
  ring

/-- `O₁ = R₁(X_max)`, `X_max = (D-2)²`. -/
noncomputable def cO1 (D u : ℝ) : ℝ := cR1 D u ((D - 2) ^ 2)
/-- `O₂ = P₁(X_max)`. -/
noncomputable def cO2 (D u : ℝ) : ℝ := cP1 D u ((D - 2) ^ 2)
/-- `O₃ = (u+3)⁴ P₁(X_min2)`. -/
noncomputable def cO3 (D u : ℝ) : ℝ :=
  (u + 3) ^ 4 * cP1 D u ((u + 2) * (u + 4) * ((D + 3) ^ 2 - (u + 3) ^ 2) / (u + 3) ^ 2)
/-- `O₄ = (D+u+4)² (K² - disc₂)/(u+2)` at `X_max`. -/
noncomputable def cO4 (D u : ℝ) : ℝ := cO4X D u ((D - 2) ^ 2)

/-- §7 table: after `D = (30/7)(u+3)² - 3 + v`, `u = w + 1`, `cO1` is a polynomial in
`(w, v)` (on the region `w, v ≥ 0`, which determines it) with exactly 24 nonzero terms, all coefficients positive, least coefficient `2`. -/
theorem cO1_table :
    ∃ L : List ((ℕ × ℕ) × ℚ), L.length = 24 ∧ (L.map Prod.fst).Nodup ∧ (∀ t ∈ L, (2 : ℚ) ≤ t.2) ∧
      (∃ t ∈ L, t.2 = 2) ∧
      ∀ w v : ℝ, 0 ≤ w → 0 ≤ v → cO1 ((30 / 7) * (w + 1 + 3) ^ 2 - 3 + v) (w + 1) =
        (L.map (fun t => (t.2 : ℝ) * w ^ t.1.1 * v ^ t.1.2)).sum := by
  refine ⟨cO1Witness, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [cO1Witness]
  · norm_num [cO1Witness]
  · norm_num [cO1Witness]
  · refine ⟨((2, 3), (2 : ℚ)), ?_, by norm_num⟩
    norm_num [cO1Witness]
  · intro w v hw hv
    unfold cO1 cR1
    simp [cO1Witness]
    ring

/-- §7 table: after `D = (30/7)(u+3)² - 3 + v`, `u = w + 1`, `cO2` is a polynomial in
`(w, v)` (on the region `w, v ≥ 0`, which determines it) with exactly 48 nonzero terms, all coefficients positive, least coefficient `10`. -/
theorem cO2_table :
    ∃ L : List ((ℕ × ℕ) × ℚ), L.length = 48 ∧ (L.map Prod.fst).Nodup ∧ (∀ t ∈ L, (10 : ℚ) ≤ t.2) ∧
      (∃ t ∈ L, t.2 = 10) ∧
      ∀ w v : ℝ, 0 ≤ w → 0 ≤ v → cO2 ((30 / 7) * (w + 1 + 3) ^ 2 - 3 + v) (w + 1) =
        (L.map (fun t => (t.2 : ℝ) * w ^ t.1.1 * v ^ t.1.2)).sum := by
  refine ⟨cO2Witness, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [cO2Witness]
  · norm_num [cO2Witness]
  · norm_num [cO2Witness]
  · refine ⟨((2, 5), (10 : ℚ)), ?_, by norm_num⟩
    norm_num [cO2Witness]
  · intro w v hw hv
    unfold cO2 cP1
    simp [cO2Witness]
    ring

/-- §7 table: after `D = (30/7)(u+3)² - 3 + v`, `u = w + 1`, `cO3` is a polynomial in
`(w, v)` (on the region `w, v ≥ 0`, which determines it) with exactly 77 nonzero terms, all coefficients positive, least coefficient `1`. -/
theorem cO3_table :
    ∃ L : List ((ℕ × ℕ) × ℚ), L.length = 77 ∧ (L.map Prod.fst).Nodup ∧ (∀ t ∈ L, (1 : ℚ) ≤ t.2) ∧
      (∃ t ∈ L, t.2 = 1) ∧
      ∀ w v : ℝ, 0 ≤ w → 0 ≤ v → cO3 ((30 / 7) * (w + 1 + 3) ^ 2 - 3 + v) (w + 1) =
        (L.map (fun t => (t.2 : ℝ) * w ^ t.1.1 * v ^ t.1.2)).sum := by
  refine ⟨cO3Witness, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [cO3Witness]
  · norm_num [cO3Witness]
  · norm_num [cO3Witness]
  · refine ⟨((4, 6), (1 : ℚ)), ?_, by norm_num⟩
    norm_num [cO3Witness]
  · intro w v hw hv
    have hden : w + 1 + 3 ≠ 0 := by positivity
    unfold cO3 cP1
    field_simp [hden]
    simp [cO3Witness]
    ring

/-- §7 table: after `D = (30/7)(u+3)² - 3 + v`, `u = w + 1`, `cO4` is a polynomial in
`(w, v)` (on the region `w, v ≥ 0`, which determines it) with exactly 30 nonzero terms, all coefficients positive, least coefficient `1`. -/
theorem cO4_table :
    ∃ L : List ((ℕ × ℕ) × ℚ), L.length = 30 ∧ (L.map Prod.fst).Nodup ∧ (∀ t ∈ L, (1 : ℚ) ≤ t.2) ∧
      (∃ t ∈ L, t.2 = 1) ∧
      ∀ w v : ℝ, 0 ≤ w → 0 ≤ v → cO4 ((30 / 7) * (w + 1 + 3) ^ 2 - 3 + v) (w + 1) =
        (L.map (fun t => (t.2 : ℝ) * w ^ t.1.1 * v ^ t.1.2)).sum := by
  refine ⟨cO4Witness, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [cO4Witness]
  · norm_num [cO4Witness]
  · norm_num [cO4Witness]
  · refine ⟨((1, 4), (1 : ℚ)), ?_, by norm_num⟩
    norm_num [cO4Witness]
  · intro w v hw hv
    unfold cO4 cO4X
    simp [cO4Witness]
    ring

end Kraw
