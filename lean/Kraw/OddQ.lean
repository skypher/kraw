import Kraw.QuadForm
import Kraw.GapStrip
import Kraw.OddCert

/-!
# Gap cells with odd `Q`

Paper Proposition 5.1 (`u = 1`), Lemma 5.2 (window transition certificate) and
Theorem 5.3 (window propagation).
-/

namespace Kraw

set_option maxHeartbeats 1000000

variable (M Q : ℕ)

def oddDisc (D x r : ℝ) : ℝ := oddCertDisc₁ D r (x ^ 2)

noncomputable def oddYPlusRad (D x r g : ℝ) : ℝ :=
  (D + 2) * (x * (r + 1) + g) /
    (r * (D + r + 4))

noncomputable def oddYMinusRad (D x r g : ℝ) : ℝ :=
  (D + 2) * (x * (r + 1) - g) /
    (r * (D + r + 4))

noncomputable def oddYPlus (D x r : ℝ) : ℝ :=
  oddYPlusRad D x r (Real.sqrt (oddDisc D x r))

noncomputable def oddYMinus (D x r : ℝ) : ℝ :=
  oddYMinusRad D x r (Real.sqrt (oddDisc D x r))

noncomputable def oddKappa (D r : ℝ) : ℝ := (D - r) / (D + r + 4)

noncomputable def oddPhi (D x r y : ℝ) : ℝ :=
  (1 + oddKappa D r) * x - oddKappa D r * (D + 2) ^ 2 / y

noncomputable def oddPhiInf (D x r : ℝ) : ℝ := (1 + oddKappa D r) * x

def oddWindow (D x r y : ℝ) : ℝ :=
  r * (D + r + 4) * y ^ 2 - 2 * (D + 2) * x * (r + 1) * y +
    (r + 2) * (D - r + 2) * (D + 2) ^ 2

lemma oddYPlus_pos {D x r : ℝ} (hr : 0 < r) (hden : 0 < D + r + 4)
    (hD2 : 0 < D + 2) (hx : 0 < x) : 0 < oddYPlus D x r := by
  unfold oddYPlus oddYPlusRad
  apply div_pos
  · apply mul_pos hD2
    have hx' : 0 < x * (r + 1) := mul_pos hx (by linarith)
    linarith [Real.sqrt_nonneg (oddDisc D x r)]
  · exact mul_pos hr hden

lemma oddWindow_factor {D x r y : ℝ} (hr : 0 < r) (hD : 0 < D + r + 4)
    (hdisc : 0 ≤ oddDisc D x r) :
    oddWindow D x r y = r * (D + r + 4) *
      (y - oddYMinus D x r) * (y - oddYPlus D x r) := by
  have hden : r * (D + r + 4) ≠ 0 := (mul_pos hr hD).ne'
  let g := Real.sqrt (oddDisc D x r)
  have hgsq : g ^ 2 = x ^ 2 * (r + 1) ^ 2 -
      r * (r + 2) * ((D + 3) ^ 2 - (r + 1) ^ 2) := by
    dsimp [g]
    rw [Real.sq_sqrt hdisc]
    rfl
  have hminus : oddYMinus D x r = oddYMinusRad D x r g := by rfl
  have hplus : oddYPlus D x r = oddYPlusRad D x r g := by rfl
  rw [hminus, hplus]
  unfold oddWindow oddYMinusRad oddYPlusRad
  field_simp [hden]
  ring_nf at hgsq
  ring_nf
  rw [hgsq]
  ring

lemma oddYMinus_le_oddYPlus {D x r : ℝ} (hr : 0 < r) (hD : 0 < D + r + 4)
    (hD2 : 0 ≤ D + 2) (_hdisc : 0 ≤ oddDisc D x r) :
    oddYMinus D x r ≤ oddYPlus D x r := by
  unfold oddYMinus oddYPlus
  apply div_le_div_of_nonneg_right _ (le_of_lt (mul_pos hr hD))
  have hs : 0 ≤ Real.sqrt (oddDisc D x r) := Real.sqrt_nonneg _
  have hp := mul_nonneg hD2 hs
  nlinarith

lemma oddWindow_nonneg_of_ge {D x r y : ℝ} (hr : 0 < r)
    (hD : 0 < D + r + 4) (hD2 : 0 ≤ D + 2)
    (hdisc : 0 ≤ oddDisc D x r) (hy : oddYPlus D x r ≤ y) :
    0 ≤ oddWindow D x r y := by
  rw [oddWindow_factor hr hD hdisc]
  have hroots := oddYMinus_le_oddYPlus hr hD hD2 hdisc
  have h₁ : 0 ≤ y - oddYMinus D x r := by linarith
  have h₂ : 0 ≤ y - oddYPlus D x r := by linarith
  exact mul_nonneg (mul_nonneg (mul_nonneg hr.le hD.le) h₁) h₂

lemma oddCertP_nonneg_between {D u X : ℝ} (hu : 1 ≤ u) (hreg :
    30 * (u + 3) ^ 2 ≤ 7 * (D + 3)) (hDu : u < D)
    (hspan : oddCertXmin D u < (D - 2) ^ 2)
    (hmin : oddCertXmin D u ≤ X) (hmax : X ≤ (D - 2) ^ 2) :
    0 ≤ oddCertP D u X := by
  have hPmin' := oddCert_pmin_nonneg hu hreg
  have hLpos : 0 < u + 3 := by linarith
  have hPmin : 0 ≤ oddCertP D u (oddCertXmin D u) :=
    nonneg_of_mul_nonneg_right hPmin' (pow_pos hLpos 4)
  have hPmax := oddCert_pmax_nonneg hu hreg
  have hR : (D - 2) ^ 2 - oddCertXmin D u > 0 := by linarith
  let a := 8 * (u + 2) * (u + 1) ^ 2 * (u - D) * (D + u + 6)
  have hDplus : 0 < D + u + 6 := by linarith
  have hapos : 0 ≤ 8 * (u + 2) * (u + 1) ^ 2 * (D + u + 6) := by positivity
  have ha : a ≤ 0 := by
    dsimp [a]
    calc
      _ = (8 * (u + 2) * (u + 1) ^ 2 * (D + u + 6)) * (u - D) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hapos (sub_nonpos.mpr hDu.le)
  have hinterp : ((D - 2) ^ 2 - oddCertXmin D u) * oddCertP D u X =
      ((D - 2) ^ 2 - X) * oddCertP D u (oddCertXmin D u) +
        (X - oddCertXmin D u) * oddCertP D u ((D - 2) ^ 2) +
        ((D - 2) ^ 2 - oddCertXmin D u) * a *
          (X - oddCertXmin D u) * (X - (D - 2) ^ 2) := by
    dsimp [a, oddCertP, oddCertA, oddCertDen, oddCertDisc₁, oddCertDisc₂]
    ring
  have hlow : 0 ≤ (D - 2) ^ 2 - X := by linarith
  have hprod : (X - oddCertXmin D u) * (X - (D - 2) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hmin) (sub_nonpos.mpr hmax)
  have hcurve : 0 ≤ a * ((X - oddCertXmin D u) * (X - (D - 2) ^ 2)) :=
    mul_nonneg_of_nonpos_of_nonpos ha hprod
  have hsum : 0 ≤ ((D - 2) ^ 2 - X) * oddCertP D u (oddCertXmin D u) +
      (X - oddCertXmin D u) * oddCertP D u ((D - 2) ^ 2) +
      ((D - 2) ^ 2 - oddCertXmin D u) * a *
        (X - oddCertXmin D u) * (X - (D - 2) ^ 2) := by
    have h₁ : 0 ≤ ((D - 2) ^ 2 - X) * oddCertP D u (oddCertXmin D u) :=
      mul_nonneg hlow hPmin
    have h₂ : 0 ≤ (X - oddCertXmin D u) * oddCertP D u ((D - 2) ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hmin) hPmax
    have h₃ : 0 ≤ ((D - 2) ^ 2 - oddCertXmin D u) *
        a * (X - oddCertXmin D u) * (X - (D - 2) ^ 2) := by
      calc
        _ = ((D - 2) ^ 2 - oddCertXmin D u) *
            (a * ((X - oddCertXmin D u) * (X - (D - 2) ^ 2))) := by ring
        _ ≥ 0 := mul_nonneg hR.le hcurve
    exact add_nonneg (add_nonneg h₁ h₂) h₃
  have hmul : 0 ≤ ((D - 2) ^ 2 - oddCertXmin D u) * oddCertP D u X := by
    rw [hinterp]
    exact hsum
  exact nonneg_of_mul_nonneg_right hmul hR

lemma oddCertR_nonneg_left {D u X : ℝ} (hu : 1 ≤ u) (hreg :
    30 * (u + 3) ^ 2 ≤ 7 * (D + 3)) (hDu : u < D)
    (hmax : X ≤ (D - 2) ^ 2) : 0 ≤ oddCertR D u X := by
  have hRmax := oddCert_rmax_nonneg hu hreg
  let a := 4 * (u + 2) * (u + 1) * (u - D) * (D + u + 6)
  have hDplus : 0 < D + u + 6 := by linarith
  have hapos : 0 ≤ 4 * (u + 2) * (u + 1) * (D + u + 6) := by positivity
  have ha : a ≤ 0 := by
    dsimp [a]
    calc
      _ = (4 * (u + 2) * (u + 1) * (D + u + 6)) * (u - D) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hapos (sub_nonpos.mpr hDu.le)
  have hlin : oddCertR D u X =
      oddCertR D u ((D - 2) ^ 2) + a * (X - (D - 2) ^ 2) := by
    dsimp [a, oddCertR, oddCertA, oddCertDen, oddCertDisc₁, oddCertDisc₂]
    ring
  have hlast : 0 ≤ a * (X - (D - 2) ^ 2) :=
    mul_nonneg_of_nonpos_of_nonpos ha (sub_nonpos.mpr hmax)
  rw [hlin]
  linarith

lemma oddCertO₄_nonneg_left {D u X : ℝ} (hu : 1 ≤ u) (hreg :
    30 * (u + 3) ^ 2 ≤ 7 * (D + 3)) (hDu : u < D)
    (hmax : X ≤ (D - 2) ^ 2) : 0 ≤ oddCertO₄ D u X := by
  have hOmax := oddCert_o4max_nonneg hu hreg
  let a := 4 * (u + 2) * (u - D) * (D + u + 6)
  have hDplus : 0 < D + u + 6 := by linarith
  have hapos : 0 ≤ 4 * (u + 2) * (D + u + 6) := by positivity
  have ha : a ≤ 0 := by
    dsimp [a]
    calc
      _ = (4 * (u + 2) * (D + u + 6)) * (u - D) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hapos (sub_nonpos.mpr hDu.le)
  have hlin : oddCertO₄ D u X =
      oddCertO₄ D u ((D - 2) ^ 2) + a * (X - (D - 2) ^ 2) := by
    dsimp [a, oddCertO₄, oddCertDen, oddCertDisc₂]
    ring
  have hlast : 0 ≤ a * (X - (D - 2) ^ 2) :=
    mul_nonneg_of_nonpos_of_nonpos ha (sub_nonpos.mpr hmax)
  rw [hlin]
  linarith

lemma oddTransition_finite {D x u y : ℝ} (hu : 1 ≤ u)
    (hreg : 30 * (u + 3) ^ 2 ≤ 7 * (D + 3)) (hDu : u < D)
    (hx : 0 < x) (hxmax : x ≤ D - 2)
    (hgap : u * (u + 2) * ((D + 3) ^ 2 - (u + 1) ^ 2) <
      x ^ 2 * (u + 1) ^ 2)
    (hgapNext : (u + 2) * (u + 4) * ((D + 3) ^ 2 - (u + 3) ^ 2) <
      x ^ 2 * (u + 3) ^ 2)
    (hy : oddYPlus D x u ≤ y) :
    oddYPlus D x (u + 2) ≤ oddPhi D x u y := by
  have hu1 : 0 < u + 1 := by linarith
  have hu2 : 0 < u + 2 := by linarith
  have hu3 : 0 < u + 3 := by linarith
  have hD : 0 < D := by linarith
  have hD2 : 0 < D + 2 := by linarith
  have hd₂ : 0 < D + u + 6 := by linarith
  let X := x ^ 2
  let d := D + u + 4
  let d₂ := D + u + 6
  let Acoef := (u + 1) * D + u ^ 2 + 9 * u + 12
  let K := x * Acoef / d
  let g₁ := Real.sqrt (oddCertDisc₁ D u X)
  let g₂ := Real.sqrt (oddCertDisc₂ D u X)
  let W := x * (u + 1) + g₁
  let B₀ := u * (D - u)
  let C₀ := (u + 2) * d₂
  have hd : 0 < d := by dsimp [d]; linarith
  have hd₂' : 0 < d₂ := by dsimp [d₂]; linarith
  have hdisc₁ : 0 < oddDisc D x u := by
    unfold oddDisc oddCertDisc₁
    nlinarith [hgap]
  have hdisc₂ : 0 < oddDisc D x (u + 2) := by
    unfold oddDisc oddCertDisc₁
    nlinarith [hgapNext]
  have hdisc₂eq : oddDisc D x (u + 2) = oddCertDisc₂ D u X := by
    dsimp [oddDisc, oddCertDisc₁, oddCertDisc₂, X]
    ring
  have hDreg : u < D := hDu
  have hmax : X ≤ (D - 2) ^ 2 := by
    have h₁ : 0 ≤ D - 2 - x := sub_nonneg.mpr hxmax
    have h₂ : 0 ≤ D - 2 + x := by linarith [hx]
    dsimp [X]
    nlinarith [mul_nonneg h₁ h₂]
  have hmin : oddCertXmin D u < X := by
    unfold oddCertXmin
    rw [div_lt_iff₀ (pow_pos hu3 2)]
    exact hgapNext
  have hspan : oddCertXmin D u < (D - 2) ^ 2 := lt_of_lt_of_le hmin hmax
  have hP : 0 ≤ oddCertP D u X :=
    oddCertP_nonneg_between hu hreg hDreg hspan (le_of_lt hmin) hmax
  have hR : 0 ≤ oddCertR D u X := oddCertR_nonneg_left hu hreg hDreg hmax
  have hcoef : 0 < Acoef := by dsimp [Acoef]; positivity
  have hK : 0 < K := by dsimp [K]; exact div_pos (mul_pos hx hcoef) hd
  have hg₁ : 0 ≤ g₁ := by dsimp [g₁]; exact Real.sqrt_nonneg _
  have hg₂ : 0 ≤ g₂ := by dsimp [g₂]; exact Real.sqrt_nonneg _
  have hg₁sq : g₁ ^ 2 = oddCertDisc₁ D u X := by
    dsimp [g₁]
    exact Real.sq_sqrt (by simpa [X, oddDisc] using hdisc₁.le)
  have hg₂sq : g₂ ^ 2 = oddCertDisc₂ D u X := by
    dsimp [g₂]
    exact Real.sq_sqrt (by rw [← hdisc₂eq]; exact hdisc₂.le)
  have hW : 0 < W := by
    dsimp [W]
    have : 0 < x * (u + 1) := mul_pos hx hu1
    linarith
  have hy₀ : oddYPlus D x u = (D + 2) * W / (u * d) := by rfl
  have hy₂ : oddYPlus D x (u + 2) = (D + 2) *
      (x * (u + 3) + g₂) / ((u + 2) * d₂) := by
    unfold oddYPlus oddYPlusRad
    rw [hdisc₂eq]
    dsimp [g₂, d₂]
    congr 1 <;> ring
  have hBnd : u * (u + 2) * ((D + 3) ^ 2 - (u + 1) ^ 2) /
      (u + 1) ^ 2 < X := by
    rw [div_lt_iff₀ (pow_pos hu1 2)]
    exact hgap
  have hboundary : (u * (u + 2) * ((D + 3) ^ 2 - (u + 1) ^ 2) /
        (u + 1) ^ 2) * Acoef * (u + 1) / d - B₀ * C₀ =
      4 * u * (D + 3) * (u + 2) ^ 2 / (u + 1) := by
    dsimp [Acoef, d, B₀, C₀, d₂]
    field_simp [ne_of_gt hu1, ne_of_gt hd]
    ring
  have hfacpos : 0 < Acoef * (u + 1) / d := div_pos (mul_pos hcoef hu1) hd
  have hbase : B₀ * C₀ < X * Acoef * (u + 1) / d := by
    have hstep := mul_lt_mul_of_pos_right hBnd hfacpos
    have hconst : 0 < 4 * u * (D + 3) * (u + 2) ^ 2 / (u + 1) := by positivity
    have hstep' : (u * (u + 2) * ((D + 3) ^ 2 - (u + 1) ^ 2) /
        (u + 1) ^ 2) * Acoef * (u + 1) / d < X * Acoef * (u + 1) / d := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep
    linarith
  have hKbase : K * x * (u + 1) = X * Acoef * (u + 1) / d := by
    dsimp [K, X]
    field_simp [ne_of_gt hd]
  have hWlower : x * (u + 1) ≤ W := by
    dsimp [W]
    exact le_add_of_nonneg_right hg₁
  have hKW : K * x * (u + 1) ≤ K * W := by
    calc
      K * x * (u + 1) = K * (x * (u + 1)) := by ring
      _ ≤ K * W := mul_le_mul_of_nonneg_left hWlower hK.le
  have hA : 0 < K * W - B₀ * C₀ := by nlinarith [hbase, hKbase, hKW]
  have hAId : oddCertA D u X + x * Acoef * g₁ = d * (K * W - B₀ * C₀) := by
    dsimp [oddCertA, oddCertDen, K, W, Acoef, B₀, C₀, d, d₂, X]
    field_simp [ne_of_gt hd]
    ring
  have hcert := oddCert_transition_identity (D := D) (u := u) (x := x) (g := g₁) hg₁sq
  have hcert' : d ^ 2 * ((K * W - B₀ * C₀) ^ 2 -
      oddDisc D x (u + 2) * W ^ 2) = oddCertP D u X +
        2 * x * oddCertR D u X * g₁ := by
    rw [hdisc₂eq]
    calc
      _ = (d * (K * W - B₀ * C₀)) ^ 2 -
          d ^ 2 * oddCertDisc₂ D u X * W ^ 2 := by ring
      _ = (oddCertA D u X + x * Acoef * g₁) ^ 2 -
          d ^ 2 * oddCertDisc₂ D u X * W ^ 2 := by rw [← hAId]
      _ = _ := hcert
  have hscaled : 0 ≤ d ^ 2 * ((K * W - B₀ * C₀) ^ 2 -
      oddDisc D x (u + 2) * W ^ 2) := by
    rw [hcert']
    exact add_nonneg hP (by positivity)
  have hsqDiff : 0 ≤ (K * W - B₀ * C₀) ^ 2 -
      oddDisc D x (u + 2) * W ^ 2 :=
    nonneg_of_mul_nonneg_right hscaled (sq_pos_of_pos hd)
  have hBsq : (g₂ * W) ^ 2 = oddDisc D x (u + 2) * W ^ 2 := by
    calc
      _ = g₂ ^ 2 * W ^ 2 := by ring
      _ = _ := by rw [hg₂sq, hdisc₂eq]
  have hAsq : (g₂ * W) ^ 2 ≤ (K * W - B₀ * C₀) ^ 2 := by
    rw [hBsq]
    linarith
  have hAupper : g₂ * W ≤ K * W - B₀ * C₀ :=
    (sq_le_sq₀ (mul_nonneg hg₂ hW.le) hA.le).mp hAsq
  have hclear : (oddPhi D x u (oddYPlus D x u) - oddYPlus D x (u + 2)) *
        (W * u * d * (u + 2) * d₂ / (D + 2)) =
      u * d * (K * W - B₀ * C₀ - g₂ * W) := by
    rw [hy₀, hy₂]
    unfold oddPhi oddKappa
    dsimp [d, d₂, K, W, Acoef, B₀, C₀]
    field_simp [ne_of_gt hu1, ne_of_gt hu2, ne_of_gt hd, ne_of_gt hd₂',
      ne_of_gt hD2, ne_of_gt hW]
    ring
  have hfactor : 0 < W * u * d * (u + 2) * d₂ / (D + 2) := by
    positivity
  have hboundaryNonneg : 0 ≤ oddPhi D x u (oddYPlus D x u) - oddYPlus D x (u + 2) := by
    apply nonneg_of_mul_nonneg_left _ hfactor
    rw [hclear]
    have : 0 ≤ K * W - B₀ * C₀ - g₂ * W := by linarith
    positivity
  have hy₀pos : 0 < oddYPlus D x u := by
    rw [hy₀]
    positivity
  have hypos : 0 < y := lt_of_lt_of_le hy₀pos hy
  have hκ : 0 ≤ oddKappa D u := by
    unfold oddKappa
    positivity
  have hrecip : 1 / y ≤ 1 / oddYPlus D x u :=
    one_div_le_one_div_of_le hy₀pos hy
  have hterm : oddKappa D u * (D + 2) ^ 2 / y ≤
      oddKappa D u * (D + 2) ^ 2 / oddYPlus D x u := by
    simp only [div_eq_mul_inv]
    have hrecip' : y⁻¹ ≤ (oddYPlus D x u)⁻¹ := by
      simpa only [one_div] using hrecip
    exact mul_le_mul_of_nonneg_left hrecip' (by positivity)
  have hmono : oddPhi D x u (oddYPlus D x u) ≤ oddPhi D x u y := by
    unfold oddPhi
    linarith
  linarith

lemma oddTransition_infinity {D x u : ℝ} (hu : 1 ≤ u)
    (hreg : 30 * (u + 3) ^ 2 ≤ 7 * (D + 3)) (hDu : u < D)
    (hx : 0 < x) (hxmax : x ≤ D - 2)
    (hgapNext : (u + 2) * (u + 4) * ((D + 3) ^ 2 - (u + 3) ^ 2) <
      x ^ 2 * (u + 3) ^ 2) :
    oddYPlus D x (u + 2) ≤ oddPhiInf D x u := by
  have hu2 : 0 < u + 2 := by linarith
  have hu3 : 0 < u + 3 := by linarith
  have hD2 : 0 < D + 2 := by linarith [hDu]
  have hDpos : 0 < D := by linarith [hDu]
  have hd : 0 < D + u + 4 := by linarith
  have hd₂ : 0 < D + u + 6 := by linarith
  let X := x ^ 2
  let d := D + u + 4
  let d₂ := D + u + 6
  let Acoef := (u + 1) * D + u ^ 2 + 9 * u + 12
  let K := x * Acoef / d
  have hdisc₂ : 0 < oddDisc D x (u + 2) := by
    unfold oddDisc oddCertDisc₁
    nlinarith [hgapNext]
  have hdisc₂eq : oddDisc D x (u + 2) = oddCertDisc₂ D u X := by
    dsimp [oddDisc, oddCertDisc₁, oddCertDisc₂, X]
    ring
  have hmax : X ≤ (D - 2) ^ 2 := by
    have h₁ : 0 ≤ D - 2 - x := sub_nonneg.mpr hxmax
    have h₂ : 0 ≤ D - 2 + x := by linarith [hx]
    dsimp [X]
    nlinarith [mul_nonneg h₁ h₂]
  have hO4 : 0 ≤ oddCertO₄ D u X := oddCertO₄_nonneg_left hu hreg hDu hmax
  have hcoef : 0 < Acoef := by dsimp [Acoef]; positivity
  have hK : 0 < K := by dsimp [K]; exact div_pos (mul_pos hx hcoef) hd
  have hO4id : oddCertO₄ D u X = d ^ 2 * (K ^ 2 -
      oddDisc D x (u + 2)) := by
    dsimp [oddCertO₄, oddCertDen, oddCertDisc₂, K, X, d, d₂, Acoef,
      oddDisc, oddCertDisc₁]
    field_simp [ne_of_gt hd]
    ring
  have hKsq : oddDisc D x (u + 2) ≤ K ^ 2 := by
    have hscaled : 0 ≤ d ^ 2 * (K ^ 2 - oddDisc D x (u + 2)) := by
      rw [← hO4id]
      exact hO4
    have hdiff : 0 ≤ K ^ 2 - oddDisc D x (u + 2) :=
      nonneg_of_mul_nonneg_right hscaled (sq_pos_of_pos hd)
    linarith
  have hroot : Real.sqrt (oddDisc D x (u + 2)) ≤ K :=
    (Real.sqrt_le_iff).2 ⟨hK.le, hKsq⟩
  have hdisc₂eq' : Real.sqrt (oddDisc D x (u + 2)) =
      Real.sqrt (oddCertDisc₂ D u X) := congrArg Real.sqrt hdisc₂eq
  have hy₂ : oddYPlus D x (u + 2) = (D + 2) *
      (x * (u + 3) + Real.sqrt (oddDisc D x (u + 2))) / ((u + 2) * d₂) := by
    unfold oddYPlus oddYPlusRad
    dsimp [d₂]
    congr 1 <;> ring
  have hdiff : oddPhiInf D x u - oddYPlus D x (u + 2) =
      (D + 2) * (K - Real.sqrt (oddDisc D x (u + 2))) /
        ((u + 2) * d₂) := by
    rw [hy₂]
    unfold oddPhiInf oddKappa
    dsimp [d, d₂, K, Acoef]
    field_simp [ne_of_gt hd, ne_of_gt hd₂, ne_of_gt hu2]
    ring
  have hnonneg : 0 ≤ (D + 2) * (K - Real.sqrt (oddDisc D x (u + 2))) /
      ((u + 2) * d₂) := by
    apply div_nonneg
    · exact mul_nonneg hD2.le (sub_nonneg.mpr hroot)
    · positivity
  exact sub_nonneg.mp (by rw [hdiff]; exact hnonneg)

/-- Lemma 5.2, odd-`D` base: nonnegativity of the cleared base polynomial. -/
lemma oddBase_nonneg {D x : ℝ} (hD : 0 ≤ D) (hx : 0 ≤ x) (hxD : x ≤ D) :
    0 ≤ oddCertBaseS D x := by
  rw [oddCertBaseS_factor]
  have h1 : 0 ≤ D + 4 - x := by linarith
  have h2 : 0 ≤ D + 2 + x := by linarith
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
    (mul_nonneg h1 h2)

lemma oddBase_odd {D x : ℝ} (hD : 0 ≤ D) (hx : 0 < x)
    (hbase : 0 ≤ oddCertBaseS D x) (hdisc : 0 ≤ oddDisc D x 1) :
    oddYPlus D x 1 ≤ (D + 2) * (2 * x + D + 1) / (D + 3) := by
  have hD3 : 0 < D + 3 := by linarith
  have hD5 : 0 < D + 5 := by linarith
  let num := 4 * x + (D + 1) * (D + 5)
  have hnum : 0 < num := by dsimp [num]; positivity
  have hbaseId : oddCertBaseS D x = num ^ 2 -
      oddDisc D x 1 * (D + 3) ^ 2 := by
    dsimp [oddCertBaseS, num, oddDisc, oddCertDisc₁]
    ring
  have hsq : oddDisc D x 1 ≤ (num / (D + 3)) ^ 2 := by
    rw [div_pow]
    rw [le_div_iff₀ (sq_pos_of_pos hD3)]
    rw [hbaseId] at hbase
    nlinarith [hbase]
  have hroot : Real.sqrt (oddDisc D x 1) ≤ num / (D + 3) :=
    (Real.sqrt_le_iff).2 ⟨div_nonneg hnum.le hD3.le, hsq⟩
  have hroot' : (D + 3) * Real.sqrt (oddDisc D x 1) ≤ num :=
    calc
      _ = Real.sqrt (oddDisc D x 1) * (D + 3) := by ring
      _ ≤ num := (le_div_iff₀ hD3).mp hroot
  unfold oddYPlus oddYPlusRad
  field_simp [ne_of_gt hD3, ne_of_gt hD5]
  dsimp [num] at hroot'
  nlinarith [hroot']

lemma oddGap_lower_real {D x r : ℤ} (hg : Gap D x r) :
    (r : ℝ) * ((r : ℝ) + 2) * (((D : ℝ) + 3) ^ 2 - ((r : ℝ) + 1) ^ 2) <
      (x : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 := by
  have hcoef : (r + 1) ^ 2 - 1 = r * (r + 2) := by ring
  have h := hg.2.1
  rw [hcoef] at h
  exact_mod_cast h

lemma oddBase_even {D x : ℝ} (hD : 0 ≤ D) (hx : 0 < x)
    (hxmax : x ≤ D - 2) (hdisc : 0 ≤ oddDisc D x 2) :
    oddYPlus D x 2 ≤ 2 * (D + 2) * x / (D + 4) := by
  have hD4 : 0 < D + 4 := by linarith
  have hD6 : 0 < D + 6 := by linarith
  have hD2 : 0 < D + 2 := by linarith
  have hx_sq : x ^ 2 ≤ (D + 4) ^ 2 := by
    have h₁ : 0 ≤ D - 2 - x := sub_nonneg.mpr hxmax
    have h₂ : 0 ≤ D - 2 + x := by linarith [hx]
    nlinarith [mul_nonneg h₁ h₂]
  have hrootSq : oddDisc D x 2 ≤ (((D + 12) * x) / (D + 4)) ^ 2 := by
    rw [div_pow]
    rw [le_div_iff₀ (sq_pos_of_pos hD4)]
    have hfact : (D + 12) ^ 2 * x ^ 2 - (D + 4) ^ 2 *
        (9 * x ^ 2 - 8 * D * (D + 6)) =
        8 * D * (D + 6) * ((D + 4) ^ 2 - x ^ 2) := by ring
    have hfact_nonneg : 0 ≤ 8 * D * (D + 6) * ((D + 4) ^ 2 - x ^ 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD) (by linarith))
        (sub_nonneg.mpr hx_sq)
    unfold oddDisc oddCertDisc₁
    nlinarith [hfact, hfact_nonneg]
  have hroot : Real.sqrt (oddDisc D x 2) ≤ ((D + 12) * x) / (D + 4) :=
    (Real.sqrt_le_iff).2 ⟨by positivity, hrootSq⟩
  have hroot' : (D + 4) * Real.sqrt (oddDisc D x 2) ≤ (D + 12) * x :=
    calc
      _ = Real.sqrt (oddDisc D x 2) * (D + 4) := by ring
      _ ≤ (D + 12) * x := (le_div_iff₀ hD4).mp hroot
  have hcmp : (D + 4) * (3 * x + Real.sqrt (oddDisc D x 2)) ≤
      4 * (D + 6) * x := by nlinarith [hroot']
  unfold oddYPlus oddYPlusRad
  field_simp [ne_of_gt hD4, ne_of_gt hD6]
  nlinarith [hcmp]

def OddProjectiveState (D x r a b : ℝ) : Prop :=
  (a = 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ oddYPlus D x r ≤ (D + 2) * b / a)

lemma oddProjective_step {D x r j a b c : ℝ}
    (hrel : 2 * j - D = r) (hjpos : 0 < j + 2) (hD2 : 0 < D + 2)
    (hrootpos : 0 < oddYPlus D x r)
    (hstate : OddProjectiveState D x r a b)
    (hrec : (j + 2) * c = x * b + (j - D) * a)
    (hfinite : ∀ y, oddYPlus D x r ≤ y →
      oddYPlus D x (r + 2) ≤ oddPhi D x r y)
    (hinfinity : oddYPlus D x (r + 2) ≤ oddPhiInf D x r) :
    OddProjectiveState D x (r + 2) b c := by
  rcases hstate with ⟨ha, hb⟩ | ⟨ha, hy⟩
  · right
    constructor
    · exact hb
    · have hrec' : (j + 2) * c = x * b := by simpa [ha] using hrec
      have hratio : (D + 2) * c / b = (D + 2) * x / (j + 2) := by
        field_simp [hb, hjpos.ne']
        nlinarith [hrec']
      have hinf : oddPhiInf D x r = (D + 2) * x / (j + 2) := by
        have hd : D + r + 4 = 2 * (j + 2) := by nlinarith [hrel]
        have hnum : D - r = 2 * (D - j) := by linarith [hrel]
        unfold oddPhiInf oddKappa
        rw [hd, hnum]
        field_simp [hjpos.ne']
        ring
      rw [hratio, ← hinf]
      exact hinfinity
  · right
    let y := (D + 2) * b / a
    change oddYPlus D x r ≤ y at hy
    have hb : b ≠ 0 := by
      intro hb0
      have hy0 : y = 0 := by dsimp [y]; simp [hb0]
      rw [hy0] at hy
      linarith [hrootpos]
    constructor
    · exact hb
    ·
      have hd : D + r + 4 = 2 * (j + 2) := by nlinarith [hrel]
      have hratio : (D + 2) * c / b = oddPhi D x r y := by
        have hphi : oddPhi D x r y =
            (D + 2) * x / (j + 2) +
              (D + 2) * (j - D) * a / ((j + 2) * b) := by
          dsimp [y]
          unfold oddPhi oddKappa
          have hnum : D - r = 2 * (D - j) := by linarith [hrel]
          rw [hd, hnum]
          field_simp [ha, hb, hjpos.ne', hD2.ne']
          ring
        rw [hphi]
        field_simp [hb, hjpos.ne']
        nlinarith [hrec]
      have hnew := hfinite y hy
      rw [hratio]
      exact hnew

lemma oddProjective_path (M Q : ℕ) {D x u j₀ s r₀ : ℤ} {n : ℕ}
    (hD : D = (M : ℤ) + Q) (hx : x = (M : ℤ) - Q)
    (hDxy : D = x + 2 * Q) (hQ : 1 ≤ (Q : ℤ))
    (hD0 : 0 ≤ D) (hx0 : 0 ≤ x) (hxD : x ≤ D)
    (hg : Gap D x u) (hj₀ : 0 ≤ j₀) (hr₀ : 1 ≤ r₀)
    (hrel₀ : 2 * j₀ - D = r₀) (hend : u = r₀ + 2 * n)
    (hindex : s = j₀ + n)
    (hstate₀ : OddProjectiveState (D : ℝ) (x : ℝ) (r₀ : ℝ)
      (p M Q j₀ : ℝ) (p M Q (j₀ + 1) : ℝ)) :
    OddProjectiveState (D : ℝ) (x : ℝ) (u : ℝ)
      (p M Q s : ℝ) (p M Q (s + 1) : ℝ) := by
  have hQ0 : 0 ≤ (Q : ℤ) := by omega
  have hstripZ := gap_strip hg hQ0 hx0 hDxy
  have hstripR : 6 * (2 * (Q : ℝ) + 3) * ((u : ℝ) + 1) ^ 2 <
      7 * ((D : ℝ) + 3) := by exact_mod_cast hstripZ
  have hxpos : 0 < x := gap_x_pos hg hD0 hx0
  have hxD2 : x ≤ D - 2 := by omega
  have hxposR : 0 < (x : ℝ) := by exact_mod_cast hxpos
  have hQ1R : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hD2R : 0 < (D : ℝ) + 2 := by exact_mod_cast (show 0 < D + 2 by omega)
  have path : ∀ k : ℕ, k ≤ n →
      OddProjectiveState (D : ℝ) (x : ℝ)
        ((r₀ + 2 * (k : ℤ) : ℤ) : ℝ)
        (p M Q (j₀ + (k : ℤ)) : ℝ)
        (p M Q (j₀ + (k : ℤ) + 1) : ℝ) := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa using hstate₀
    | succ k ih =>
        intro hk
        have hklt : k < n := by omega
        have hprev := ih (by omega)
        let rI : ℤ := r₀ + 2 * (k : ℤ)
        let jI : ℤ := j₀ + (k : ℤ)
        have hprev' : OddProjectiveState (D : ℝ) (x : ℝ) (rI : ℝ)
            (p M Q jI : ℝ) (p M Q (jI + 1) : ℝ) := by
          simpa [rI, jI] using hprev
        have hrI : 1 ≤ rI := by dsimp [rI]; omega
        have hrI2 : rI + 2 ≤ u := by
          rw [hend]
          dsimp [rI]
          omega
        have hgI : Gap D x rI :=
          gap_hered hg hD0 hx0 hxD hrI (by omega)
        have hgI2 : Gap D x (rI + 2) :=
          gap_hered hg hD0 hx0 hxD (by omega) hrI2
        have hgapI := oddGap_lower_real hgI
        have hgapI2 := oddGap_lower_real hgI2
        let rr : ℝ := (rI : ℝ)
        have hrposR : 0 < rr := by
          dsimp [rr]
          exact_mod_cast (show 0 < rI by omega)
        have hrOneR : 1 ≤ rr := by
          dsimp [rr]
          exact_mod_cast hrI
        have hRbound : rr + 3 ≤ (u : ℝ) + 1 := by
          have hZ : rI + 3 ≤ u + 1 := by omega
          dsimp [rr]
          exact_mod_cast hZ
        have hRsq : (rr + 3) ^ 2 ≤ ((u : ℝ) + 1) ^ 2 := by
          have hu1R : 0 ≤ (u : ℝ) + 1 := by
            have hz : 0 ≤ u + 1 := by rw [hend]; omega
            exact_mod_cast hz
          have hsum : 0 ≤ ((u : ℝ) + 1) + (rr + 3) := by linarith [hu1R, hrOneR]
          nlinarith [mul_nonneg (sub_nonneg.mpr hRbound) hsum]
        have hcoef : 30 ≤ 6 * (2 * (Q : ℝ) + 3) := by nlinarith [hQ1R]
        have hreg : 30 * (rr + 3) ^ 2 ≤ 7 * ((D : ℝ) + 3) := by
          have hmul₁ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (rr + 3))
          have hqcoef0 : 0 ≤ 6 * (2 * (Q : ℝ) + 3) := le_trans (by norm_num) hcoef
          have hmul₂ := mul_le_mul_of_nonneg_left hRsq hqcoef0
          exact le_of_lt (lt_of_le_of_lt (by linarith [hmul₁, hmul₂]) hstripR)
        have hflowI : (rI + 1 : ℤ) ^ 2 < (D + 1) ^ 2 - x ^ 2 := hgI.2.2
        have hflowIR : (rr + 1) ^ 2 < ((D : ℝ) + 1) ^ 2 - (x : ℝ) ^ 2 := by
          dsimp [rr]
          exact_mod_cast hflowI
        have hsqIR : (rr + 1) ^ 2 < ((D : ℝ) + 1) ^ 2 :=
          lt_of_lt_of_le hflowIR (by nlinarith [sq_nonneg (x : ℝ)])
        have hrI1R : 0 ≤ rr + 1 := by linarith [hrposR]
        have hD1R : 0 ≤ (D : ℝ) + 1 := by positivity
        have hrID : rr < (D : ℝ) := by
          have hlt := (sq_lt_sq₀ hrI1R hD1R).mp hsqIR
          linarith
        have hxiMaxR : (x : ℝ) ≤ (D : ℝ) - 2 := by exact_mod_cast hxD2
        have hgapIR : rr * (rr + 2) *
            (((D : ℝ) + 3) ^ 2 - (rr + 1) ^ 2) <
            (x : ℝ) ^ 2 * (rr + 1) ^ 2 := by
          simpa [rr] using hgapI
        have hgapI2R : (rr + 2) * (rr + 4) *
            (((D : ℝ) + 3) ^ 2 - (rr + 3) ^ 2) <
            (x : ℝ) ^ 2 * (rr + 3) ^ 2 := by
          have h := hgapI2
          push_cast at h
          dsimp [rr] at h ⊢
          ring_nf at h ⊢
          exact h
        have hrootpos : 0 < oddYPlus (D : ℝ) (x : ℝ) rr :=
          oddYPlus_pos hrposR (by positivity) hD2R hxposR
        have hrelI : 2 * (jI : ℝ) - (D : ℝ) = rr := by
          have hz : 2 * jI - D = rI := by
            dsimp [jI, rI]
            omega
          dsimp [rr]
          exact_mod_cast hz
        have hrecZ : (jI + 2) * p M Q (jI + 2) =
            x * p M Q (jI + 1) + (jI - D) * p M Q jI := by
          have h := p_rec M Q (jI + 1)
          rw [← hx, ← hD] at h
          simpa only [show jI + 1 + 1 = jI + 2 by omega,
            show jI + 1 - 1 = jI by omega,
            show jI + 1 - 1 - D = jI - D by omega] using h
        have hrecR : ((jI : ℝ) + 2) * (p M Q (jI + 2) : ℝ) =
            (x : ℝ) * (p M Q (jI + 1) : ℝ) +
              ((jI : ℝ) - (D : ℝ)) * (p M Q jI : ℝ) := by exact_mod_cast hrecZ
        have hjposR : 0 < (jI : ℝ) + 2 := by
          have hz : 0 < jI + 2 := by dsimp [jI]; omega
          exact_mod_cast hz
        have hfinite : ∀ y, oddYPlus (D : ℝ) (x : ℝ) rr ≤ y →
            oddYPlus (D : ℝ) (x : ℝ) (rr + 2) ≤
              oddPhi (D : ℝ) (x : ℝ) rr y := by
          intro y hy
          have h := oddTransition_finite (D := (D : ℝ)) (x := (x : ℝ)) (u := rr)
            hrOneR hreg hrID hxposR hxiMaxR hgapIR hgapI2R hy
          exact h
        have hinfinity : oddYPlus (D : ℝ) (x : ℝ) (rr + 2) ≤
            oddPhiInf (D : ℝ) (x : ℝ) rr := by
          have h := oddTransition_infinity (D := (D : ℝ)) (x := (x : ℝ)) (u := rr)
            hrOneR hreg hrID hxposR hxiMaxR hgapI2R
          exact h
        have hstep := oddProjective_step hrelI hjposR hD2R hrootpos hprev'
          hrecR hfinite hinfinity
        have hoffZ : r₀ + 2 * ((k + 1 : ℕ) : ℤ) = rI + 2 := by
          dsimp [rI]
          push_cast
          ring
        have hoffR : ((r₀ + 2 * ((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) =
            (rI : ℝ) + 2 := by exact_mod_cast hoffZ
        have hindZ : j₀ + ((k + 1 : ℕ) : ℤ) = jI + 1 := by
          dsimp [jI]
          push_cast
          ring
        rw [hoffR, hindZ]
        simpa only [show jI + 1 + 1 = jI + 2 by omega] using hstep
  have hfinal := path n le_rfl
  rw [hend, hindex]
  simpa [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hfinal

/-- Proposition 5.1: for odd `Q` and `u = 1`,
`T_s = 32 (M+1)(Q+2) p_s^2 / ((D+3)^2 (D+5)) ≥ 0`. -/
theorem T_odd_u1 (hQ : Odd Q) {s : ℤ} (hs : 2 * s = (M : ℤ) + Q + 1) : 0 ≤ T M Q s := by
  have hreflect : p M Q (s - 1) = -p M Q s := by
    have hidx : (M : ℤ) + Q - s = s - 1 := by omega
    have hpow : (-1 : ℤ) ^ Q = -1 := Odd.neg_one_pow hQ
    rw [← hidx, p_refl]
    rw [hpow]
    ring
  have hp1 : (s + 1) * p M Q (s + 1) = (2 * (M : ℤ) - s + 1) * p M Q s := by
    rw [p_rec M Q s, hreflect]
    ring
  have hp2 : (s + 2) * p M Q (s + 2) =
      ((M : ℤ) - Q) * p M Q (s + 1) + (s - ((M : ℤ) + Q)) * p M Q s := by
    simpa only [show s + 1 + 1 = s + 2 by omega,
      show s + 1 - 1 = s by omega] using p_rec M Q (s + 1)
  have hT : T M Q s = p M Q s ^ 2 + p M Q s * p M Q (s + 1) -
      p M Q (s + 1) ^ 2 + p M Q s * p M Q (s + 2) := by
    simp [T, Tur, hreflect]
    ring
  have hp01 : (s + 1) * p M Q s * p M Q (s + 1) =
      (2 * (M : ℤ) - s + 1) * p M Q s ^ 2 := by
    calc
      _ = p M Q s * ((s + 1) * p M Q (s + 1)) := by ring
      _ = p M Q s * ((2 * (M : ℤ) - s + 1) * p M Q s) := by rw [hp1]
      _ = _ := by ring
  have hp11 : (s + 1) ^ 2 * p M Q (s + 1) ^ 2 =
      (2 * (M : ℤ) - s + 1) ^ 2 * p M Q s ^ 2 := by
    calc
      _ = ((s + 1) * p M Q (s + 1)) ^ 2 := by ring
      _ = ((2 * (M : ℤ) - s + 1) * p M Q s) ^ 2 := by rw [hp1]
      _ = _ := by ring
  have hp01' : (s + 1) ^ 2 * p M Q s * p M Q (s + 1) =
      (s + 1) * (2 * (M : ℤ) - s + 1) * p M Q s ^ 2 := by
    calc
      _ = (s + 1) * ((s + 1) * p M Q s * p M Q (s + 1)) := by ring
      _ = _ := by rw [hp01]; ring
  have hp02 : (s + 2) * (s + 1) ^ 2 * p M Q s * p M Q (s + 2) =
      ((M : ℤ) - Q) * (s + 1) * (2 * (M : ℤ) - s + 1) * p M Q s ^ 2 +
        (s - ((M : ℤ) + Q)) * (s + 1) ^ 2 * p M Q s ^ 2 := by
    calc
      _ = (s + 1) ^ 2 * p M Q s * ((s + 2) * p M Q (s + 2)) := by ring
      _ = (s + 1) ^ 2 * p M Q s *
          (((M : ℤ) - Q) * p M Q (s + 1) +
            (s - ((M : ℤ) + Q)) * p M Q s) := by
          exact congrArg (fun z : ℤ => (s + 1) ^ 2 * p M Q s * z) hp2
      _ = ((M : ℤ) - Q) * ((s + 1) ^ 2 * p M Q s * p M Q (s + 1)) +
          (s - ((M : ℤ) + Q)) * (s + 1) ^ 2 * p M Q s ^ 2 := by ring
      _ = _ := by rw [hp01']; ring
  have hid : (s + 1) ^ 2 * (s + 2) * T M Q s =
      4 * ((M : ℤ) + 1) * (Q + 2) * p M Q s ^ 2 := by
    rw [hT]
    calc
      _ = (s + 1) ^ 2 * (s + 2) * p M Q s ^ 2 +
          (s + 2) * ((s + 1) ^ 2 * p M Q s * p M Q (s + 1)) -
          (s + 2) * ((s + 1) ^ 2 * p M Q (s + 1) ^ 2) +
          (s + 2) * (s + 1) ^ 2 * p M Q s * p M Q (s + 2) := by ring
      _ = _ := by
        rw [hp01', hp11, hp02]
        have hQcast : (Q : ℤ) = 2 * s - (M : ℤ) - 1 := by omega
        rw [hQcast]
        ring
  have hs1 : 0 < s + 1 := by omega
  have hs2 : 0 < s + 2 := by omega
  have hcoef : 0 ≤ 4 * ((M : ℤ) + 1) * (Q + 2) := by positivity
  have hsquare : 0 ≤ p M Q s ^ 2 := sq_nonneg _
  have hprod : 0 ≤ 4 * ((M : ℤ) + 1) * (Q + 2) * p M Q s ^ 2 :=
    mul_nonneg hcoef hsquare
  have hden : 0 < (s + 1) ^ 2 * (s + 2) := mul_pos (sq_pos_of_pos hs1) hs2
  have hmul : 0 ≤ ((s + 1) ^ 2 * (s + 2)) * T M Q s := by
    rw [hid]
    exact hprod
  exact nonneg_of_mul_nonneg_right hmul hden

/-- Theorem 5.3: if `Q ≤ M` and `Q` is odd, every gap cell with `u ≥ 2` has `T_s ≥ 0`. -/
theorem T_nonneg_gap_odd (hQM : Q ≤ M) (hQ : Odd Q) {s : ℤ} (hs : s ≤ (M : ℤ) + Q)
    (hu : 2 ≤ 2 * s - ((M : ℤ) + Q))
    (hg : Gap ((M : ℤ) + Q) ((M : ℤ) - Q) (2 * s - ((M : ℤ) + Q))) :
    0 ≤ T M Q s := by
  let D : ℤ := (M : ℤ) + Q
  let x : ℤ := (M : ℤ) - Q
  let u : ℤ := 2 * s - D
  have hDdef : D = (M : ℤ) + Q := rfl
  have hxdef : x = (M : ℤ) - Q := rfl
  have hQMZ : (Q : ℤ) ≤ M := by exact_mod_cast hQM
  have hQpos : 0 < Q := by
    rcases hQ with ⟨k, hk⟩
    omega
  have hQone : 1 ≤ (Q : ℤ) := by exact_mod_cast (Nat.succ_le_of_lt hQpos)
  have hD0 : 0 ≤ D := by dsimp [D]; omega
  have hx0 : 0 ≤ x := by dsimp [x]; omega
  have hxD : x ≤ D := by dsimp [D, x]; omega
  have hDxy : D = x + 2 * (Q : ℤ) := by dsimp [D, x]; omega
  have hxD2 : x ≤ D - 2 := by omega
  have huD : 2 ≤ u := by simpa [u, D] using hu
  have hsD : s ≤ D := by simpa [D] using hs
  have hgD : Gap D x u := by simpa [D, x, u] using hg
  have hxpos : 0 < x := gap_x_pos hgD hD0 hx0
  have hxposR : 0 < (x : ℝ) := by exact_mod_cast hxpos
  have hxD2R : (x : ℝ) ≤ (D : ℝ) - 2 := by exact_mod_cast hxD2
  have hD0R : 0 ≤ (D : ℝ) := by exact_mod_cast hD0
  have hQ0 : 0 ≤ (Q : ℤ) := by omega
  have hstripZ := gap_strip hgD hQ0 hx0 hDxy
  have hstripR : 6 * (2 * (Q : ℝ) + 3) * ((u : ℝ) + 1) ^ 2 <
      7 * ((D : ℝ) + 3) := by exact_mod_cast hstripZ
  have hQoneR : 1 ≤ (Q : ℝ) := by exact_mod_cast hQone
  have hpow : (-1 : ℤ) ^ Q = -1 := Odd.neg_one_pow hQ
  have hrecCenter (c : ℤ) :
      (c + 2) * p M Q (c + 2) =
        ((M : ℤ) - Q) * p M Q (c + 1) +
          (c - ((M : ℤ) + Q)) * p M Q c := by
    simpa only [show c + 1 + 1 = c + 2 by omega,
      show c + 1 - 1 = c by omega] using p_rec M Q (c + 1)
  have htarget : OddProjectiveState (D : ℝ) (x : ℝ) (u : ℝ)
      (p M Q s : ℝ) (p M Q (s + 1) : ℝ) := by
    rcases Int.even_or_odd' D with ⟨c, hpar | hpar⟩
    · have hDpar : (M : ℤ) + Q = 2 * c := by
        calc
          (M : ℤ) + Q = D := hDdef.symm
          _ = 2 * c := hpar
      have hc0 : 0 ≤ c := by
        have : 0 ≤ 2 * c := by rw [← hpar]; exact hD0
        omega
      have hcTop : c ≤ (M : ℤ) + Q := by rw [hDpar]; omega
      have hidx : (M : ℤ) + Q - c = c := by omega
      have hreflect := p_refl M Q c
      rw [hidx, hpow] at hreflect
      have hpc : p M Q c = 0 := by nlinarith [hreflect]
      have hpc1ne : p M Q (c + 1) ≠ 0 := by
        intro hzero
        exact (no_consec_zero M Q hc0 hcTop) ⟨hpc, hzero⟩
      have hrec0 : (c + 2) * p M Q (c + 2) =
          ((M : ℤ) - Q) * p M Q (c + 1) := by
        simpa [hpc] using hrecCenter c
      have hDreal : (D : ℝ) = 2 * (c : ℝ) := by exact_mod_cast hpar
      have hcpos : 0 < (c : ℝ) + 2 := by exact_mod_cast (show 0 < c + 2 by omega)
      have hpc1Rne : (p M Q (c + 1) : ℝ) ≠ 0 := by exact_mod_cast hpc1ne
      have hrec0R : ((c : ℝ) + 2) * (p M Q (c + 2) : ℝ) =
          (x : ℝ) * (p M Q (c + 1) : ℝ) := by
        have h := congrArg (fun z : ℤ => (z : ℝ)) hrec0
        push_cast at h
        simpa [hxdef, add_assoc] using h
      have hratio : ((D : ℝ) + 2) * (p M Q (c + 2) : ℝ) /
          (p M Q (c + 1) : ℝ) =
            2 * ((D : ℝ) + 2) * (x : ℝ) / ((D : ℝ) + 4) := by
        rw [hDreal]
        field_simp [hpc1Rne, hcpos.ne']
        nlinarith [hrec0R]
      have hgap2 : Gap D x 2 :=
        gap_hered hgD hD0 hx0 hxD (by norm_num) (by omega)
      have hdisc2 : 0 ≤ oddDisc (D : ℝ) (x : ℝ) 2 := by
        have h := oddGap_lower_real hgap2
        unfold oddDisc oddCertDisc₁
        norm_num at h ⊢
        nlinarith [h]
      have hstate0 : OddProjectiveState (D : ℝ) (x : ℝ) (2 : ℝ)
          (p M Q (c + 1) : ℝ) (p M Q (c + 2) : ℝ) := by
        right
        constructor
        · exact hpc1Rne
        · rw [hratio]
          exact oddBase_even hD0R hxposR hxD2R hdisc2
      have hstatePath : OddProjectiveState (D : ℝ) (x : ℝ) ((2 : ℤ) : ℝ)
          (p M Q (c + 1) : ℝ) (p M Q (c + 1 + 1) : ℝ) := by
        simpa [show c + 1 + 1 = c + 2 by omega] using hstate0
      have huRep : u = 2 * (s - c) := by dsimp [u, D]; rw [hDpar]; ring
      have hn0 : 0 ≤ s - c - 1 := by rw [huRep] at huD; omega
      let n : ℕ := (s - c - 1).toNat
      have hn : (n : ℤ) = s - c - 1 := by
        dsimp [n]
        exact Int.toNat_of_nonneg hn0
      have hend : u = 2 + 2 * (n : ℤ) := by rw [huRep, hn]; ring
      have hindex : s = (c + 1) + (n : ℤ) := by rw [hn]; omega
      have hrel0 : 2 * (c + 1) - D = 2 := by rw [hpar]; ring
      exact oddProjective_path M Q (D := D) (x := x) (u := u)
        (j₀ := c + 1) (s := s) (r₀ := 2) (n := n)
        hDdef hxdef hDxy hQone hD0 hx0 hxD hgD (by omega) (by norm_num)
        hrel0 hend hindex hstatePath
    · have hDpar : (M : ℤ) + Q = 2 * c + 1 := by
        calc
          (M : ℤ) + Q = D := hDdef.symm
          _ = 2 * c + 1 := hpar
      have hc0 : 0 ≤ c := by
        have : 1 ≤ 2 * c + 1 := by rw [← hDpar, ← hDdef]; omega
        omega
      have hcTop : c ≤ (M : ℤ) + Q := by rw [hDpar]; omega
      have hidx : (M : ℤ) + Q - c = c + 1 := by omega
      have hreflect := p_refl M Q c
      rw [hidx, hpow] at hreflect
      have hcenter : p M Q (c + 1) = -p M Q c := by simpa using hreflect
      have hpcne : p M Q c ≠ 0 := by
        intro hp0
        have hp1 : p M Q (c + 1) = 0 := by rw [hcenter, hp0]; norm_num
        exact (no_consec_zero M Q hc0 hcTop) ⟨hp0, hp1⟩
      have hpc1ne : p M Q (c + 1) ≠ 0 := by
        intro hp1
        apply hpcne
        linarith [hcenter, hp1]
      have hpcEq : p M Q c = -p M Q (c + 1) := by linarith [hcenter]
      have hrecOdd : (c + 2) * p M Q (c + 2) =
          (((M : ℤ) - Q) + (c + 1)) * p M Q (c + 1) := by
        calc
          _ = ((M : ℤ) - Q) * p M Q (c + 1) +
              (c - ((M : ℤ) + Q)) * p M Q c := hrecCenter c
          _ = _ := by rw [hDpar, hpcEq]; ring
      have hDreal : (D : ℝ) = 2 * (c : ℝ) + 1 := by exact_mod_cast hpar
      have hcpos : 0 < (c : ℝ) + 2 := by exact_mod_cast (show 0 < c + 2 by omega)
      have hpc1Rne : (p M Q (c + 1) : ℝ) ≠ 0 := by exact_mod_cast hpc1ne
      have hrecOddR : ((c : ℝ) + 2) * (p M Q (c + 2) : ℝ) =
          ((x : ℝ) + (c : ℝ) + 1) * (p M Q (c + 1) : ℝ) := by
        have h := congrArg (fun z : ℤ => (z : ℝ)) hrecOdd
        push_cast at h
        rw [show (x : ℝ) + (c : ℝ) + 1 = (x : ℝ) + ((c : ℝ) + 1) by ring]
        rw [hxdef]
        push_cast
        exact h
      have hratio : ((D : ℝ) + 2) * (p M Q (c + 2) : ℝ) /
          (p M Q (c + 1) : ℝ) =
            ((D : ℝ) + 2) * (2 * (x : ℝ) + (D : ℝ) + 1) / ((D : ℝ) + 3) := by
        rw [hDreal]
        field_simp [hpc1Rne, hcpos.ne']
        nlinarith [hrecOddR]
      have hgap1 : Gap D x 1 :=
        gap_hered hgD hD0 hx0 hxD (by norm_num) (by omega)
      have hdisc1 : 0 ≤ oddDisc (D : ℝ) (x : ℝ) 1 := by
        have h := oddGap_lower_real hgap1
        unfold oddDisc oddCertDisc₁
        norm_num at h ⊢
        nlinarith [h]
      have hbaseS := oddBase_nonneg hD0R hxposR.le (by linarith [hxD2R])
      have hstate0 : OddProjectiveState (D : ℝ) (x : ℝ) (1 : ℝ)
          (p M Q (c + 1) : ℝ) (p M Q (c + 2) : ℝ) := by
        right
        constructor
        · exact hpc1Rne
        · rw [hratio]
          exact oddBase_odd hD0R hxposR hbaseS hdisc1
      have hstatePath : OddProjectiveState (D : ℝ) (x : ℝ) ((1 : ℤ) : ℝ)
          (p M Q (c + 1) : ℝ) (p M Q (c + 1 + 1) : ℝ) := by
        simpa [show c + 1 + 1 = c + 2 by omega] using hstate0
      have huRep : u = 2 * (s - c - 1) + 1 := by dsimp [u, D]; rw [hDpar]; ring
      have hn0 : 0 ≤ s - c - 1 := by rw [huRep] at huD; omega
      let n : ℕ := (s - c - 1).toNat
      have hn : (n : ℤ) = s - c - 1 := by
        dsimp [n]
        exact Int.toNat_of_nonneg hn0
      have hend : u = 1 + 2 * (n : ℤ) := by rw [huRep, hn]; ring
      have hindex : s = (c + 1) + (n : ℤ) := by rw [hn]; omega
      have hrel0 : 2 * (c + 1) - D = 1 := by rw [hpar]; ring
      exact oddProjective_path M Q (D := D) (x := x) (u := u)
        (j₀ := c + 1) (s := s) (r₀ := 1) (n := n)
        hDdef hxdef hDxy hQone hD0 hx0 hxD hgD (by omega) (by norm_num)
        hrel0 hend hindex hstatePath
  let d : ℝ := (D : ℝ)
  let xx : ℝ := (x : ℝ)
  let uu : ℝ := (u : ℝ)
  let ss : ℝ := (s : ℝ)
  let a : ℝ := (p M Q s : ℝ)
  let b : ℝ := (p M Q (s + 1) : ℝ)
  let t : ℝ := (T M Q s : ℝ)
  have huR : 2 ≤ uu := by
    have h : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast huD
    simpa [uu] using h
  have hsplus : 0 < ss + 2 := by
    have huExp : 2 ≤ 2 * s - D := by simpa [u] using huD
    have hz : 0 < s + 2 := by omega
    have h : (0 : ℝ) < (s : ℝ) + 2 := by exact_mod_cast hz
    simpa [ss] using h
  have hDminus : 0 < d + 1 - ss := by
    have hz : 0 < D + 1 - s := by omega
    have h : (0 : ℝ) < (D : ℝ) + 1 - (s : ℝ) := by exact_mod_cast hz
    simpa [d, ss] using h
  have hdisc : 0 ≤ oddDisc d xx uu := by
    have h := oddGap_lower_real hgD
    unfold oddDisc oddCertDisc₁
    dsimp [d, xx, uu]
    nlinarith [h]
  have hqformR : (ss + 2) * (d + 1 - ss) * t =
      (uu + 2) * (d + 1 - ss) * a ^ 2 -
        xx * (uu + 1) * a * b + uu * (ss + 2) * b ^ 2 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (qform M Q s)
    push_cast at h
    simpa [D, x, u, d, xx, uu, ss, a, b, t] using h
  rcases htarget with ⟨hzero, _⟩ | ⟨hane, hy⟩
  · have hzero' : a = 0 := by simpa [a] using hzero
    have hqzero : (ss + 2) * (d + 1 - ss) * t = uu * (ss + 2) * b ^ 2 := by
      rw [hzero'] at hqformR
      simpa using hqformR
    have hscale : 0 < (ss + 2) * (d + 1 - ss) := mul_pos hsplus hDminus
    have hmul : 0 ≤ ((ss + 2) * (d + 1 - ss)) * t := by
      rw [hqzero]
      positivity
    have ht : 0 ≤ t := nonneg_of_mul_nonneg_right hmul hscale
    have htCast : 0 ≤ (T M Q s : ℝ) := by simpa [t] using ht
    exact_mod_cast htCast
  · have haneq : a ≠ 0 := by simpa [a] using hane
    have hroot : oddYPlus d xx uu ≤ (d + 2) * b / a := by
      simpa [d, xx, uu, a, b] using hy
    have hru : 0 < uu := by linarith [huR]
    have hden : 0 < d + uu + 4 := by positivity
    have hwindow : 0 ≤ oddWindow d xx uu ((d + 2) * b / a) :=
      oddWindow_nonneg_of_ge hru hden (by positivity) hdisc hroot
    have hrel : 2 * ss = d + uu := by
      dsimp [ss, d, uu, u, D]
      push_cast
      ring
    have hden1 : d + uu + 4 = 2 * (ss + 2) := by linarith [hrel]
    have hden2 : d - uu + 2 = 2 * (d + 1 - ss) := by linarith [hrel]
    have hwindowId : oddWindow d xx uu ((d + 2) * b / a) * a ^ 2 =
        2 * (d + 2) ^ 2 *
          ((uu + 2) * (d + 1 - ss) * a ^ 2 - xx * (uu + 1) * a * b +
            uu * (ss + 2) * b ^ 2) := by
      unfold oddWindow
      rw [hden1, hden2]
      field_simp [haneq]
      ring
    have hscale : oddWindow d xx uu ((d + 2) * b / a) * a ^ 2 =
        2 * (ss + 2) * (d + 1 - ss) * (d + 2) ^ 2 * t := by
      calc
        _ = 2 * (d + 2) ^ 2 *
            ((uu + 2) * (d + 1 - ss) * a ^ 2 - xx * (uu + 1) * a * b +
              uu * (ss + 2) * b ^ 2) := hwindowId
        _ = 2 * (d + 2) ^ 2 * ((ss + 2) * (d + 1 - ss) * t) := by rw [← hqformR]
        _ = _ := by ring
    have hscalePos : 0 < 2 * (ss + 2) * (d + 1 - ss) * (d + 2) ^ 2 := by positivity
    have hmul : 0 ≤ (2 * (ss + 2) * (d + 1 - ss) * (d + 2) ^ 2) * t := by
      rw [← hscale]
      exact mul_nonneg hwindow (sq_nonneg a)
    have ht : 0 ≤ t := nonneg_of_mul_nonneg_right hmul hscalePos
    have htCast : 0 ≤ (T M Q s : ℝ) := by simpa [t] using ht
    exact_mod_cast htCast

end Kraw
