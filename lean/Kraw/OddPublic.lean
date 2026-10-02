import Kraw.OddQ

/-!
# Paper §5 in the paper's notation: Proposition 5.1, the window (5.1), Lemma 5.2
-/

namespace Kraw

set_option maxHeartbeats 1000000

/-- Proposition 5.1: for odd `Q` and `2s = D+1`, `(D+3)²(D+5) T_s = 32(M+1)(Q+2) p_s²`. -/
theorem prop_5_1 (M Q : ℕ) (hQ : Odd Q) {s : ℤ} (hs : 2 * s = (M : ℤ) + Q + 1) :
    ((M : ℤ) + Q + 3) ^ 2 * ((M : ℤ) + Q + 5) * T M Q s = 32 * ((M : ℤ) + 1) * ((Q : ℤ) + 2) * p M Q s ^ 2 := by
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
      _ = p M Q s * ((s + 1) * p M Q (s + 1) : ℤ) := by ring
      _ = p M Q s * ((2 * (M : ℤ) - s + 1) * p M Q s) := by rw [hp1]
      _ = _ := by ring
  have hp11 : (s + 1) ^ 2 * p M Q (s + 1) ^ 2 =
      (2 * (M : ℤ) - s + 1) ^ 2 * p M Q s ^ 2 := by
    calc
      _ = ((s + 1) * p M Q (s + 1)) ^ 2 := by ring
      _ = ((2 * (M : ℤ) - s + 1) * p M Q s) ^ 2 := by rw [hp1]
      _ = _ := by ring_nf
  have hp01' : (s + 1) ^ 2 * p M Q s * p M Q (s + 1) =
      (s + 1) * (2 * (M : ℤ) - s + 1) * p M Q s ^ 2 := by
    calc
      _ = (s + 1) * ((s + 1) * p M Q s * p M Q (s + 1)) := by ring
      _ = (s + 1) * ((2 * (M : ℤ) - s + 1) * p M Q s ^ 2) := by rw [hp01]
      _ = _ := by ring
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
      4 * ((M : ℤ) + 1) * ((Q : ℤ) + 2) * p M Q s ^ 2 := by
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
  have hD3 : (M : ℤ) + Q + 3 = 2 * (s + 1) := by omega
  have hD5 : (M : ℤ) + Q + 5 = 2 * (s + 2) := by omega
  calc
    _ = (2 * (s + 1)) ^ 2 * (2 * (s + 2)) * T M Q s := by rw [← hD3, ← hD5]
    _ = 8 * ((s + 1) ^ 2 * (s + 2) * T M Q s) := by ring
    _ = 32 * ((M : ℤ) + 1) * ((Q : ℤ) + 2) * p M Q s ^ 2 := by rw [hid]; ring

/-- The window polynomial (5.1), with `u = 2s - D`. -/
noncomputable def windowG (D x s y : ℝ) : ℝ :=
  (2 * s - D) * (s + 2) * y ^ 2 - x * (2 * s - D + 1) * (D + 2) * y +
    (2 * s - D + 2) * (D + 1 - s) * (D + 2) ^ 2

/-- (5.1): `G(y_s) p_s² = (s+2)(D+1-s)(D+2)² T_s` with `y_s = (D+2) p_{s+1}/p_s`. -/
theorem window_identity (M Q : ℕ) (s : ℤ) (hp : p M Q s ≠ 0) :
    windowG ((M : ℝ) + Q) ((M : ℝ) - Q) s (((M : ℝ) + Q + 2) * p M Q (s + 1) / p M Q s) *
        (p M Q s : ℝ) ^ 2 =
      ((s : ℝ) + 2) * ((M : ℝ) + Q + 1 - s) * ((M : ℝ) + Q + 2) ^ 2 * T M Q s := by
  have hq := qform M Q s
  have hqR : ((s : ℝ) + 2) * ((M : ℝ) + Q + 1 - s) * (T M Q s : ℝ) =
      (2 * (s : ℝ) - ((M : ℝ) + Q) + 2) * ((M : ℝ) + Q + 1 - s) *
          (p M Q s : ℝ) ^ 2 -
        ((M : ℝ) - Q) * (2 * (s : ℝ) - ((M : ℝ) + Q) + 1) *
          (p M Q s : ℝ) * (p M Q (s + 1) : ℝ) +
        (2 * (s : ℝ) - ((M : ℝ) + Q)) * ((s : ℝ) + 2) *
          (p M Q (s + 1) : ℝ) ^ 2 := by
    exact_mod_cast hq
  have hpR : (p M Q s : ℝ) ≠ 0 := by exact_mod_cast hp
  have hqScaled := congrArg (fun z : ℝ => ((M : ℝ) + Q + 2) ^ 2 * z) hqR
  rw [windowG]
  field_simp [hpR]
  nlinarith [hqScaled]

/-- §5: the discriminant of `G` is `(D+2)² q(U)`. -/
theorem window_disc (D x s : ℝ) :
    (x * (2 * s - D + 1) * (D + 2)) ^ 2 -
        4 * ((2 * s - D) * (s + 2)) * ((2 * s - D + 2) * (D + 1 - s) * (D + 2) ^ 2) =
      (D + 2) ^ 2 * (x ^ 2 * (2 * s - D + 1) ^ 2 -
        ((2 * s - D + 1) ^ 2 - 1) * ((D + 3) ^ 2 - (2 * s - D + 1) ^ 2)) := by
  ring

/-- (5.2): `g_r`. -/
noncomputable def gWin (D x r : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 * (r + 1) ^ 2 - r * (r + 2) * ((D + 3) ^ 2 - (r + 1) ^ 2))

/-- (5.2): the upper window endpoint `y_+(r)`. -/
noncomputable def yPlus (D x r : ℝ) : ℝ := (D + 2) * (x * (r + 1) + gWin D x r) / (r * (D + r + 4))

/-- (5.2): `κ(r)`. -/
noncomputable def kappa (D r : ℝ) : ℝ := (D - r) / (D + r + 4)

/-- (5.2): `Φ_r(y)`. -/
noncomputable def Phi (D x r y : ℝ) : ℝ := (1 + kappa D r) * x - kappa D r * (D + 2) ^ 2 / y

private lemma oddTransition_finite_closed {D x u y : ℝ} (hu : 1 ≤ u)
    (hreg : 30 * (u + 3) ^ 2 ≤ 7 * (D + 3)) (hDu : u < D)
    (hx : 0 < x) (hxmax : x ≤ D - 2)
    (hdisc₁ : 0 ≤ oddDisc D x u) (hdisc₂ : 0 ≤ oddDisc D x (u + 2))
    (hy : oddYPlus D x u ≤ y) : oddYPlus D x (u + 2) ≤ oddPhi D x u y := by
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
  have hdisc₂eq : oddDisc D x (u + 2) = oddCertDisc₂ D u X := by
    dsimp [oddDisc, oddCertDisc₁, oddCertDisc₂, X]
    ring
  have hmax : X ≤ (D - 2) ^ 2 := by
    have h₁ : 0 ≤ D - 2 - x := sub_nonneg.mpr hxmax
    have h₂ : 0 ≤ D - 2 + x := by linarith [hx]
    dsimp [X]
    nlinarith [mul_nonneg h₁ h₂]
  have hmin : oddCertXmin D u ≤ X := by
    have hdisc₂' : 0 ≤ X * (u + 3) ^ 2 -
        (u + 2) * (u + 4) * ((D + 3) ^ 2 - (u + 3) ^ 2) := by
      have htmp : 0 ≤ oddCertDisc₂ D u X := by rw [← hdisc₂eq]; exact hdisc₂
      simpa only [oddCertDisc₂] using htmp
    unfold oddCertXmin
    rw [div_le_iff₀ (pow_pos hu3 2)]
    nlinarith [hdisc₂']
  have hP : 0 ≤ oddCertP D u X := by
    by_cases hspan : oddCertXmin D u < (D - 2) ^ 2
    · exact oddCertP_nonneg_between hu hreg hDu hspan hmin hmax
    · have hle : oddCertXmin D u ≤ (D - 2) ^ 2 := le_trans hmin hmax
      have heq : oddCertXmin D u = (D - 2) ^ 2 :=
        le_antisymm hle (le_of_not_gt hspan)
      have hX : X = (D - 2) ^ 2 := by
        apply le_antisymm hmax
        simpa [heq] using hmin
      simpa [hX] using oddCert_pmax_nonneg hu hreg
  have hR : 0 ≤ oddCertR D u X := oddCertR_nonneg_left hu hreg hDu hmax
  have hcoef : 0 < Acoef := by dsimp [Acoef]; positivity
  have hK : 0 < K := by dsimp [K]; exact div_pos (mul_pos hx hcoef) hd
  have hg₁ : 0 ≤ g₁ := by dsimp [g₁]; exact Real.sqrt_nonneg _
  have hg₂ : 0 ≤ g₂ := by dsimp [g₂]; exact Real.sqrt_nonneg _
  have hg₁sq : g₁ ^ 2 = oddCertDisc₁ D u X := by
    dsimp [g₁]
    have hdisc₁' : 0 ≤ oddCertDisc₁ D u X := by
      simpa [oddDisc, X] using hdisc₁
    exact Real.sq_sqrt hdisc₁'
  have hg₂sq : g₂ ^ 2 = oddCertDisc₂ D u X := by
    dsimp [g₂]
    exact Real.sq_sqrt (by rw [← hdisc₂eq]; exact hdisc₂)
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
      (u + 1) ^ 2 ≤ X := by
    have hdisc₁' : 0 ≤ X * (u + 1) ^ 2 -
        u * (u + 2) * ((D + 3) ^ 2 - (u + 1) ^ 2) := by
      simpa [oddDisc, oddCertDisc₁, X] using hdisc₁
    rw [div_le_iff₀ (pow_pos hu1 2)]
    dsimp [X]
    nlinarith [hdisc₁']
  have hboundary : (u * (u + 2) * ((D + 3) ^ 2 - (u + 1) ^ 2) /
        (u + 1) ^ 2) * Acoef * (u + 1) / d - B₀ * C₀ =
      4 * u * (D + 3) * (u + 2) ^ 2 / (u + 1) := by
    dsimp [Acoef, d, B₀, C₀, d₂]
    field_simp [ne_of_gt hu1, ne_of_gt hd]
    ring
  have hfacpos : 0 < Acoef * (u + 1) / d := div_pos (mul_pos hcoef hu1) hd
  have hconst : 0 < 4 * u * (D + 3) * (u + 2) ^ 2 / (u + 1) := by positivity
  have hbase : B₀ * C₀ < X * Acoef * (u + 1) / d := by
    have hstep := mul_le_mul_of_nonneg_right hBnd hfacpos.le
    have hstep' : (u * (u + 2) * ((D + 3) ^ 2 - (u + 1) ^ 2) /
        (u + 1) ^ 2) * Acoef * (u + 1) / d ≤ X * Acoef * (u + 1) / d := by
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
  have hfactor : 0 < W * u * d * (u + 2) * d₂ / (D + 2) := by positivity
  have hboundaryNonneg : 0 ≤ oddPhi D x u (oddYPlus D x u) - oddYPlus D x (u + 2) := by
    apply nonneg_of_mul_nonneg_left _ hfactor
    rw [hclear]
    have : 0 ≤ K * W - B₀ * C₀ - g₂ * W := by linarith
    positivity
  have hy₀pos : 0 < oddYPlus D x u := by rw [hy₀]; positivity
  have hypos : 0 < y := lt_of_lt_of_le hy₀pos hy
  have hκ : 0 ≤ oddKappa D u := by unfold oddKappa; positivity
  have hrecip : 1 / y ≤ 1 / oddYPlus D x u := one_div_le_one_div_of_le hy₀pos hy
  have hterm : oddKappa D u * (D + 2) ^ 2 / y ≤
      oddKappa D u * (D + 2) ^ 2 / oddYPlus D x u := by
    simp only [div_eq_mul_inv]
    have hrecip' : y⁻¹ ≤ (oddYPlus D x u)⁻¹ := by
      simpa only [one_div] using hrecip
    have hcoeff : 0 ≤ oddKappa D u * (D + 2) ^ 2 := mul_nonneg hκ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left hrecip' hcoeff
  have hmono : oddPhi D x u (oddYPlus D x u) ≤ oddPhi D x u y := by
    unfold oddPhi
    linarith
  linarith

private lemma oddTransition_infinity_closed {D x u : ℝ} (hu : 1 ≤ u)
    (hreg : 30 * (u + 3) ^ 2 ≤ 7 * (D + 3)) (hDu : u < D)
    (hx : 0 < x) (hxmax : x ≤ D - 2)
    (_hdisc₂ : 0 ≤ oddDisc D x (u + 2)) :
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
  have hy₂ : oddYPlus D x (u + 2) = (D + 2) *
      (x * (u + 3) + Real.sqrt (oddDisc D x (u + 2))) / ((u + 2) * d₂) := by
    unfold oddYPlus oddYPlusRad
    dsimp [d₂]
    congr 1 <;> ring
  have hdiff : oddPhiInf D x u - oddYPlus D x (u + 2) =
      (D + 2) * (K - Real.sqrt (oddDisc D x (u + 2))) / ((u + 2) * d₂) := by
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

/-- Lemma 5.2 (transition). -/
theorem lemma_5_2 {D Q u : ℤ} (hQ : 1 ≤ Q) (hx : 0 ≤ D - 2 * Q) (hu : 1 ≤ u)
    (hreg : 30 * (u + 3) ^ 2 ≤ 7 * (D + 3))
    (hw : 0 ≤ ((D : ℝ) - 2 * Q) ^ 2 * ((u : ℝ) + 1) ^ 2 -
      (u : ℝ) * (u + 2) * (((D : ℝ) + 3) ^ 2 - ((u : ℝ) + 1) ^ 2))
    (hw2 : 0 ≤ ((D : ℝ) - 2 * Q) ^ 2 * ((u : ℝ) + 3) ^ 2 -
      ((u : ℝ) + 2) * (u + 4) * (((D : ℝ) + 3) ^ 2 - ((u : ℝ) + 3) ^ 2)) :
    (∀ y : ℝ, yPlus D (D - 2 * Q) u ≤ y →
        yPlus D (D - 2 * Q) (u + 2) ≤ Phi D (D - 2 * Q) u y) ∧
      yPlus D (D - 2 * Q) (u + 2) ≤ (1 + kappa D u) * ((D : ℝ) - 2 * Q) := by
  have hQ' : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hx' : 0 ≤ (D : ℝ) - 2 * (Q : ℝ) := by exact_mod_cast hx
  have hu' : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hreg' : 30 * ((u : ℝ) + 3) ^ 2 ≤ 7 * ((D : ℝ) + 3) := by
    exact_mod_cast hreg
  have hwin₁ : 0 ≤ ((D : ℝ) - 2 * (Q : ℝ)) ^ 2 * ((u : ℝ) + 1) ^ 2 -
      (u : ℝ) * ((u : ℝ) + 2) * (((D : ℝ) + 3) ^ 2 - ((u : ℝ) + 1) ^ 2) := by
    exact_mod_cast hw
  have hwin₂ : 0 ≤ ((D : ℝ) - 2 * (Q : ℝ)) ^ 2 * ((u : ℝ) + 3) ^ 2 -
      ((u : ℝ) + 2) * ((u : ℝ) + 4) * (((D : ℝ) + 3) ^ 2 - ((u : ℝ) + 3) ^ 2) := by
    exact_mod_cast hw2
  have hdisc₁ : 0 ≤ oddDisc (D : ℝ) ((D : ℝ) - 2 * (Q : ℝ)) (u : ℝ) := by
    simpa [oddDisc, oddCertDisc₁] using hwin₁
  have hdisc₂ : 0 ≤ oddDisc (D : ℝ) ((D : ℝ) - 2 * (Q : ℝ)) ((u : ℝ) + 2) := by
    unfold oddDisc oddCertDisc₁
    nlinarith [hwin₂]
  have hu3 : 0 < (u : ℝ) + 3 := by linarith
  have hsmall : 0 < 30 * ((u : ℝ) + 3) - 7 := by nlinarith
  have hregion : 7 * ((u : ℝ) + 3) < 30 * ((u : ℝ) + 3) ^ 2 := by
    have hp := mul_pos hu3 hsmall
    nlinarith [hp]
  have hDu : (u : ℝ) < (D : ℝ) := by
    have hcmp := lt_of_lt_of_le hregion hreg'
    linarith
  have hxpos : 0 < (D : ℝ) - 2 * (Q : ℝ) := by
    by_contra hnot
    have hxzero : (D : ℝ) - 2 * (Q : ℝ) = 0 := le_antisymm (le_of_not_gt hnot) hx'
    have hline : (u : ℝ) + 1 < (D : ℝ) + 3 := by linarith [hDu]
    have hE : ((u : ℝ) + 1) ^ 2 < ((D : ℝ) + 3) ^ 2 := by
      have huPlus : 0 < (u : ℝ) + 1 := by linarith [hu']
      have hDPlus : 0 < (D : ℝ) + 3 := by linarith [hline, huPlus]
      have hprod : 0 < (((D : ℝ) + 3) - ((u : ℝ) + 1)) *
          (((D : ℝ) + 3) + ((u : ℝ) + 1)) :=
        mul_pos (sub_pos.mpr hline) (by linarith [hDPlus, huPlus])
      nlinarith [hprod]
    have hfactor : 0 < (u : ℝ) * ((u : ℝ) + 2) *
        (((D : ℝ) + 3) ^ 2 - ((u : ℝ) + 1) ^ 2) := by positivity
    have hneg : oddDisc (D : ℝ) ((D : ℝ) - 2 * (Q : ℝ)) (u : ℝ) < 0 := by
      rw [oddDisc, oddCertDisc₁, hxzero]
      nlinarith [hfactor]
    linarith
  have hxmax : (D : ℝ) - 2 * (Q : ℝ) ≤ (D : ℝ) - 2 := by
    have hQreal : 1 ≤ (Q : ℝ) := hQ'
    linarith
  constructor
  · intro y hy
    have hy' : oddYPlus (D : ℝ) ((D : ℝ) - 2 * (Q : ℝ)) (u : ℝ) ≤ y := by
      simpa [yPlus, gWin, oddYPlus, oddYPlusRad, oddDisc, oddCertDisc₁] using hy
    have htrans := oddTransition_finite_closed hu' hreg' hDu hxpos hxmax hdisc₁ hdisc₂ hy'
    simpa [Phi, kappa, oddPhi, oddKappa, yPlus, gWin, oddYPlus, oddYPlusRad,
      oddDisc, oddCertDisc₁] using htrans
  · have hinf := oddTransition_infinity_closed hu' hreg' hDu hxpos hxmax hdisc₂
    simpa [kappa, oddKappa, oddPhiInf, yPlus, gWin, oddYPlus, oddYPlusRad,
      oddDisc, oddCertDisc₁] using hinf

/-- Lemma 5.2 (odd-`D` base). -/
theorem lemma_5_2_base {D Q : ℤ} (hD : Odd D) (hQ : 1 ≤ Q) (hx : 0 ≤ D - 2 * Q)
    (hw : 0 ≤ ((D : ℝ) - 2 * Q) ^ 2 * 4 - 3 * (((D : ℝ) + 3) ^ 2 - 4)) :
    yPlus D (D - 2 * Q) 1 ≤ ((D : ℝ) + 2) * (2 * ((D : ℝ) - 2 * Q) + D + 1) / (D + 3) := by
  have hx' : 0 ≤ (D : ℝ) - 2 * (Q : ℝ) := by exact_mod_cast hx
  have hxne : D - 2 * Q ≠ 0 := by
    intro heq
    rcases hD with ⟨k, hk⟩
    omega
  have hxposZ : 0 < D - 2 * Q := by omega
  have hxpos : 0 < (D : ℝ) - 2 * (Q : ℝ) := by exact_mod_cast hxposZ
  have hD0Z : 0 ≤ D := by omega
  have hD0 : 0 ≤ (D : ℝ) := by exact_mod_cast hD0Z
  have hQ' : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hxD : (D : ℝ) - 2 * (Q : ℝ) ≤ (D : ℝ) := by linarith
  have hbase : 0 ≤ oddCertBaseS (D : ℝ) ((D : ℝ) - 2 * (Q : ℝ)) :=
    oddBase_nonneg hD0 hx' hxD
  have hwin : 0 ≤ ((D : ℝ) - 2 * (Q : ℝ)) ^ 2 * 4 -
      3 * (((D : ℝ) + 3) ^ 2 - 4) := by exact_mod_cast hw
  have hdisc : 0 ≤ oddDisc (D : ℝ) ((D : ℝ) - 2 * (Q : ℝ)) 1 := by
    unfold oddDisc oddCertDisc₁
    nlinarith [hwin]
  have hbaseOdd := oddBase_odd hD0 hxpos hbase hdisc
  simpa [yPlus, gWin, oddYPlus, oddYPlusRad, oddDisc, oddCertDisc₁] using hbaseOdd

end Kraw
