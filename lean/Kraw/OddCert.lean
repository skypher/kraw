import Mathlib

namespace Kraw

def oddCertDisc₁ (D u X : ℝ) : ℝ :=
  X * (u + 1) ^ 2 - u * (u + 2) * ((D + 3) ^ 2 - (u + 1) ^ 2)

def oddCertDisc₂ (D u X : ℝ) : ℝ :=
  X * (u + 3) ^ 2 - (u + 2) * (u + 4) * ((D + 3) ^ 2 - (u + 3) ^ 2)

def oddCertDen (D u : ℝ) : ℝ := D + u + 4

def oddCertA (D u X : ℝ) : ℝ :=
  X * ((u + 1) * D + u ^ 2 + 9 * u + 12) * (u + 1) -
    u * (D - u) * (u + 2) * (D + u + 6) * oddCertDen D u

def oddCertP (D u X : ℝ) : ℝ :=
  oddCertA D u X ^ 2 + X * ((u + 1) * D + u ^ 2 + 9 * u + 12) ^ 2 *
      oddCertDisc₁ D u X -
    oddCertDen D u ^ 2 * oddCertDisc₂ D u X *
      (X * (u + 1) ^ 2 + oddCertDisc₁ D u X)

def oddCertR (D u X : ℝ) : ℝ :=
  oddCertA D u X * ((u + 1) * D + u ^ 2 + 9 * u + 12) -
    (u + 1) * oddCertDisc₂ D u X * oddCertDen D u ^ 2

def oddCertO₄ (D u X : ℝ) : ℝ :=
  X * ((u + 1) * D + u ^ 2 + 9 * u + 12) ^ 2 -
    oddCertDen D u ^ 2 * oddCertDisc₂ D u X

def oddCertBaseS (D x : ℝ) : ℝ :=
  (4 * x + (D + 1) * (D + 5)) ^ 2 -
    (4 * x ^ 2 - 3 * ((D + 3) ^ 2 - 4)) * (D + 3) ^ 2

set_option maxRecDepth 10000 in
lemma oddCert_transition_identity {D u x g : ℝ}
    (hg : g ^ 2 = oddCertDisc₁ D u (x ^ 2)) :
    (oddCertA D u (x ^ 2) +
        x * ((u + 1) * D + u ^ 2 + 9 * u + 12) * g) ^ 2 -
      oddCertDen D u ^ 2 * oddCertDisc₂ D u (x ^ 2) *
        (x * (u + 1) + g) ^ 2 =
      oddCertP D u (x ^ 2) + 2 * x * oddCertR D u (x ^ 2) * g := by
  have hg' : g ^ 2 = x ^ 2 * (u + 1) ^ 2 -
      u * (u + 2) * ((D + 3) ^ 2 - (u + 1) ^ 2) := by
    simpa only [oddCertDisc₁] using hg
  unfold oddCertP oddCertR oddCertA oddCertDen oddCertDisc₁ oddCertDisc₂
  linear_combination
    (x ^ 2 * ((u + 1) * D + u ^ 2 + 9 * u + 12) ^ 2 -
      (D + u + 4) ^ 2 * (x ^ 2 * (u + 3) ^ 2 -
        (u + 2) * (u + 4) * ((D + 3) ^ 2 - (u + 3) ^ 2))) * hg'

noncomputable def oddCertXmin (D u : ℝ) : ℝ :=
  (u + 2) * (u + 4) * ((D + 3) ^ 2 - (u + 3) ^ 2) / (u + 3) ^ 2

lemma oddCert_pmax_nonneg {D u : ℝ} (hu : 1 ≤ u)
    (hreg : 30 * (u + 3) ^ 2 ≤ 7 * (D + 3)) :
    0 ≤ oddCertP D u ((D - 2) ^ 2) := by
  let w := u - 1
  let v := D - (30 / 7 : ℝ) * (u + 3) ^ 2 + 3
  have hw : 0 ≤ w := by dsimp [w]; linarith
  have hv : 0 ≤ v := by dsimp [v]; nlinarith [hreg]
  have hu' : u = w + 1 := by dsimp [w]; ring
  have hD' : D = (30 / 7 : ℝ) * (u + 3) ^ 2 - 3 + v := by dsimp [v]; ring
  rw [hD', hu']
  dsimp [oddCertP, oddCertA, oddCertDen, oddCertDisc₁, oddCertDisc₂]
  ring_nf
  positivity

lemma oddCert_rmax_nonneg {D u : ℝ} (hu : 1 ≤ u)
    (hreg : 30 * (u + 3) ^ 2 ≤ 7 * (D + 3)) :
    0 ≤ oddCertR D u ((D - 2) ^ 2) := by
  let w := u - 1
  let v := D - (30 / 7 : ℝ) * (u + 3) ^ 2 + 3
  have hw : 0 ≤ w := by dsimp [w]; linarith
  have hv : 0 ≤ v := by dsimp [v]; nlinarith [hreg]
  have hu' : u = w + 1 := by dsimp [w]; ring
  have hD' : D = (30 / 7 : ℝ) * (u + 3) ^ 2 - 3 + v := by dsimp [v]; ring
  rw [hD', hu']
  dsimp [oddCertR, oddCertA, oddCertDen, oddCertDisc₁, oddCertDisc₂]
  ring_nf
  positivity

lemma oddCert_pmin_nonneg {D u : ℝ} (hu : 1 ≤ u)
    (hreg : 30 * (u + 3) ^ 2 ≤ 7 * (D + 3)) :
    0 ≤ (u + 3) ^ 4 * oddCertP D u (oddCertXmin D u) := by
  let w := u - 1
  let v := D - (30 / 7 : ℝ) * (u + 3) ^ 2 + 3
  have hw : 0 ≤ w := by dsimp [w]; linarith
  have hv : 0 ≤ v := by dsimp [v]; nlinarith [hreg]
  have hu' : u = w + 1 := by dsimp [w]; ring
  have hD' : D = (30 / 7 : ℝ) * (u + 3) ^ 2 - 3 + v := by dsimp [v]; ring
  have hu3 : 0 < u + 3 := by linarith
  rw [hD', hu']
  dsimp [oddCertP, oddCertA, oddCertDen, oddCertDisc₁, oddCertDisc₂,
    oddCertXmin]
  field_simp
  ring_nf
  positivity

lemma oddCert_o4max_nonneg {D u : ℝ} (hu : 1 ≤ u)
    (hreg : 30 * (u + 3) ^ 2 ≤ 7 * (D + 3)) :
    0 ≤ oddCertO₄ D u ((D - 2) ^ 2) := by
  let w := u - 1
  let v := D - (30 / 7 : ℝ) * (u + 3) ^ 2 + 3
  have hw : 0 ≤ w := by dsimp [w]; linarith
  have hv : 0 ≤ v := by dsimp [v]; nlinarith [hreg]
  have hu' : u = w + 1 := by dsimp [w]; ring
  have hD' : D = (30 / 7 : ℝ) * (u + 3) ^ 2 - 3 + v := by dsimp [v]; ring
  rw [hD', hu']
  dsimp [oddCertO₄, oddCertDen, oddCertDisc₂]
  ring_nf
  positivity

/-- Lemma 5.2, odd-`D` base: `(D+3)^2 (B_o^2 - g_1^2) = 4(D+1)(D+5)((D+3)^2-(x-1)^2)`. -/
lemma oddCertBaseS_factor (D x : ℝ) :
    oddCertBaseS D x = 4 * (D + 1) * (D + 5) * ((D + 4 - x) * (D + 2 + x)) := by
  unfold oddCertBaseS
  ring

end Kraw
