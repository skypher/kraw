import Kraw.QuadForm

/-!
# The flow region

Paper Theorem 3.3 (Riccati comparison).
-/

namespace Kraw

variable (M Q : ℕ)

private def flowRad (D x : ℝ) (k : ℕ) : ℝ :=
  x ^ 2 - 4 * (k : ℝ) * (D + 1 - k)

private noncomputable def flowPhi (D x : ℝ) (k : ℕ) : ℝ :=
  (x + Real.sqrt (flowRad D x k)) / 2

private noncomputable def flowY (D x : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => x - ((D - (k : ℝ) + 1) * k) / flowY D x k

private noncomputable def flowP (M Q : ℕ) (k : ℕ) : ℝ :=
  (p M Q ((M : ℤ) + Q - (k : ℤ)) : ℝ)

private noncomputable def flowI1 (D x k w : ℝ) : ℝ :=
  (D - 2 * k + 2) * (k + 1) * ((x + w) / 2) ^ 2 -
    x * (D - 2 * k + 1) * k * ((x + w) / 2) +
    (D - 2 * k) * (D - k + 2) * k ^ 2

private noncomputable def flowI1P (D x k : ℝ) : ℝ :=
  ((D + 2 - k) * x ^ 2 -
    2 * k * (D ^ 2 - 2 * D * k + 3 * D + 2 * k ^ 2 - 2 * k + 2)) / 2

private noncomputable def flowI1Q (D x k : ℝ) : ℝ :=
  x * (D - k + 2) / 2

private noncomputable def flowI2 (D x k w : ℝ) : ℝ :=
  x * (D - 2 * k + 1) * ((x + w) / 2) -
    2 * (D - 2 * k) * (D - k + 2) * k

private noncomputable def flowI2P (D x k : ℝ) : ℝ :=
  (x ^ 2 * (D - 2 * k + 1) -
    4 * k * (D ^ 2 - 3 * D * k + 2 * D + 2 * k ^ 2 - 4 * k)) / 2

private noncomputable def flowI2Q (D x k : ℝ) : ℝ :=
  x * (D - 2 * k + 1) / 2

private theorem flowI1_nonneg {D x k w : ℝ}
    (hx : 0 ≤ x) (hk : 1 ≤ k) (hK : 1 ≤ D - 2 * k)
    (hRad : 0 ≤ x ^ 2 - 4 * k * (D + 1 - k))
    (hw : w ^ 2 = x ^ 2 - 4 * k * (D + 1 - k)) (hw0 : 0 ≤ w) :
    0 ≤ flowI1 D x k w := by
  have hid : flowI1 D x k w = flowI1P D x k + flowI1Q D x k * w := by
    unfold flowI1 flowI1P flowI1Q
    ring_nf
    rw [hw]
    ring
  have hcoef : 0 < D + 2 - k := by nlinarith [hK, hk]
  have hPdiff : flowI1P D x k - k * (D + 2) * (D - 2 * k + 1) =
      (D + 2 - k) / 2 * (x ^ 2 - 4 * k * (D + 1 - k)) := by
    unfold flowI1P
    ring
  have hPbase : 0 ≤ k * (D + 2) * (D - 2 * k + 1) := by
    have hD2 : 0 ≤ D + 2 := by nlinarith [hK, hk]
    have hu : 0 ≤ D - 2 * k + 1 := by nlinarith [hK]
    positivity
  have hP : 0 ≤ flowI1P D x k := by
    have hcoef0 : 0 ≤ (D + 2 - k) / 2 := by positivity
    have hprod := mul_nonneg hcoef0 hRad
    nlinarith [hPdiff, hPbase, hprod]
  have hQ : 0 ≤ flowI1Q D x k := by
    have hDk : 0 ≤ D - k + 2 := by nlinarith [hK, hk]
    unfold flowI1Q
    positivity
  rw [hid]
  exact add_nonneg hP (mul_nonneg hQ hw0)

private theorem flowI2_nonneg {D x k w : ℝ}
    (hx : 0 ≤ x) (hk : 1 ≤ k) (hK : 1 ≤ D - 2 * k)
    (hRad : 0 ≤ x ^ 2 - 4 * k * (D + 1 - k))
    (hw : w ^ 2 = x ^ 2 - 4 * k * (D + 1 - k)) (hw0 : 0 ≤ w) :
    0 ≤ flowI2 D x k w := by
  have hid : flowI2 D x k w = flowI2P D x k + flowI2Q D x k * w := by
    unfold flowI2 flowI2P flowI2Q
    ring
  have hPdiff : flowI2P D x k - 2 * k * (k + 1) =
      (D - 2 * k + 1) / 2 * (x ^ 2 - 4 * k * (D + 1 - k)) := by
    unfold flowI2P
    ring
  have hPbase : 0 ≤ 2 * k * (k + 1) := by positivity
  have hP : 0 ≤ flowI2P D x k := by
    have hcoef : 0 ≤ (D - 2 * k + 1) / 2 := by positivity
    have hprod := mul_nonneg hcoef hRad
    nlinarith [hPdiff, hPbase, hprod]
  have hQ : 0 ≤ flowI2Q D x k := by
    unfold flowI2Q
    have hu : 0 ≤ D - 2 * k + 1 := by nlinarith [hK]
    positivity
  rw [hid]
  exact add_nonneg hP (mul_nonneg hQ hw0)

private theorem flowRad_tail {D x : ℝ} {n K : ℕ}
    (hn : n ≤ K) (hK : 1 ≤ D - 2 * (K : ℝ)) :
    flowRad D x K ≤ flowRad D x n := by
  have hn' : (n : ℝ) ≤ K := by exact_mod_cast hn
  have hkn : 0 ≤ (K : ℝ) - n := by linarith
  have hsum : 0 ≤ D + 1 - (n : ℝ) - K := by nlinarith
  have hid : flowRad D x n - flowRad D x K =
      4 * ((K : ℝ) - n) * (D + 1 - (n : ℝ) - K) := by
    simp [flowRad]
    ring
  rw [← sub_nonneg]
  rw [hid]
  exact mul_nonneg (mul_nonneg (by norm_num) hkn) hsum

private theorem flowRad_step (D x : ℝ) (k : ℕ) :
    flowRad D x k - flowRad D x (k + 1) = 4 * (D - 2 * (k : ℝ)) := by
  simp [flowRad]
  push_cast
  ring

private theorem flowPhi_chain {D x : ℝ} {n K : ℕ}
    (hK : 1 ≤ D - 2 * (K : ℝ))
    (hRad : 0 ≤ flowRad D x K)
    (hx : 0 < x)
    (hn : 1 ≤ n) (hnK : n ≤ K) :
    0 < flowPhi D x n := by
  have hradn : 0 ≤ flowRad D x n := (le_trans hRad (flowRad_tail (x := x) hnK hK))
  unfold flowPhi
  positivity

private theorem flowPhi_step {D x : ℝ} {n K : ℕ}
    (hK : 1 ≤ D - 2 * (K : ℝ))
    (hRad : 0 ≤ flowRad D x K)
    (hn : 1 ≤ n) (hnK : n < K) :
    flowPhi D x (n + 1) ≤ flowPhi D x n := by
  have hradn : 0 ≤ flowRad D x n :=
    le_trans hRad (flowRad_tail (x := x) (Nat.le_of_lt hnK) hK)
  have hradnext : 0 ≤ flowRad D x (n + 1) :=
    le_trans hRad (flowRad_tail (x := x) (Nat.succ_le_of_lt hnK) hK)
  have hstep := flowRad_step D x n
  have hradineq : flowRad D x (n + 1) ≤ flowRad D x n := by
    have hn' : (n : ℝ) < K := by exact_mod_cast hnK
    nlinarith
  unfold flowPhi
  have hsqrt := Real.sqrt_le_sqrt hradineq
  linarith

private theorem flowPhi_le_x {D x : ℝ} {n K : ℕ}
    (hK : 1 ≤ D - 2 * (K : ℝ))
    (hRad : 0 ≤ flowRad D x K)
    (hx : 0 ≤ x)
    (hn : 1 ≤ n) (hnK : n ≤ K) :
    flowPhi D x n ≤ x := by
  have hradn : 0 ≤ flowRad D x n :=
    le_trans hRad (flowRad_tail (x := x) hnK hK)
  have hterm : 0 ≤ 4 * (n : ℝ) * (D + 1 - n) := by
    have hn' : (n : ℝ) ≤ K := by exact_mod_cast hnK
    have hD : 0 ≤ D + 1 - n := by nlinarith [hK]
    positivity
  have hradbound : flowRad D x n ≤ x ^ 2 := by
    unfold flowRad
    linarith
  have hsqrt : Real.sqrt (flowRad D x n) ≤ x := by
    nlinarith [Real.sq_sqrt hradn]
  unfold flowPhi
  linarith

private theorem flowPhi_recurrence {D x : ℝ} {n : ℕ}
    (hRad : 0 ≤ flowRad D x n) (hphi : 0 < flowPhi D x n) :
    x - ((D - (n : ℝ) + 1) * n) / flowPhi D x n = flowPhi D x n := by
  have hsqrt : (Real.sqrt (flowRad D x n)) ^ 2 = flowRad D x n :=
    Real.sq_sqrt hRad
  have hrad : x ^ 2 - (Real.sqrt (flowRad D x n)) ^ 2 =
      4 * (D - (n : ℝ) + 1) * n := by
    unfold flowRad at *
    push_cast at *
    nlinarith
  unfold flowPhi at *
  have hden : x + Real.sqrt (flowRad D x n) ≠ 0 := by
    have hsqrt0 : 0 ≤ Real.sqrt (flowRad D x n) := Real.sqrt_nonneg _
    have : 0 < x + Real.sqrt (flowRad D x n) := by linarith
    linarith
  field_simp [hden]
  nlinarith

private theorem flowY_bound {D x : ℝ} {K : ℕ}
    (hK : 1 ≤ D - 2 * (K : ℝ))
    (hRad : 0 ≤ flowRad D x K)
    (hx : 0 < x) :
    ∀ n, 1 ≤ n → n ≤ K → flowPhi D x n ≤ flowY D x n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn hnK
      cases n with
      | zero => omega
      | succ m =>
          cases m with
          | zero =>
              have hphiX := flowPhi_le_x (n := 1) (K := K) hK hRad hx.le
                (by norm_num) hnK
              simpa [flowY] using hphiX
          | succ j =>
              have hm : 1 ≤ j + 1 := by omega
              have hmK : j + 1 ≤ K := by omega
              have hprevBound := ih (j + 1) (by omega) hm hmK
              have hprevPos := flowPhi_chain (n := j + 1) (K := K)
                hK hRad hx hm hmK
              have hprevYPos : 0 < flowY D x (j + 1) :=
                lt_of_lt_of_le hprevPos hprevBound
              have hphiStep := flowPhi_step (n := j + 1) (K := K)
                hK hRad hm (by omega)
              have hrec := flowPhi_recurrence
                (le_trans hRad (flowRad_tail (x := x) hmK hK)) hprevPos
              have hcoeff : 0 ≤ (D - ((j + 1 : ℕ) : ℝ) + 1) * (j + 1 : ℝ) := by
                have hm' : (j + 1 : ℝ) ≤ K := by exact_mod_cast hmK
                have hDlarge : 2 * (K : ℝ) + 1 ≤ D := by linarith [hK]
                have hjK : (j : ℝ) ≤ K := by linarith [hm']
                have hD : 0 ≤ D - ((j + 1 : ℕ) : ℝ) + 1 := by
                  push_cast
                  linarith [hDlarge, hjK]
                exact mul_nonneg hD (by positivity)
              have hfrac :
                  ((D - (j + 1 : ℝ) + 1) * (j + 1 : ℝ)) /
                      flowY D x (j + 1) ≤
                    ((D - (j + 1 : ℝ) + 1) * (j + 1 : ℝ)) /
                      flowPhi D x (j + 1) := by
                rw [div_le_div_iff₀ hprevYPos hprevPos]
                have hmul := mul_le_mul_of_nonneg_left hprevBound hcoeff
                push_cast at hmul ⊢
                nlinarith [hmul]
              have hmain :
                  x - ((D - (j + 1 : ℝ) + 1) * (j + 1 : ℝ)) /
                    flowY D x (j + 1) ≥
                  x - ((D - (j + 1 : ℝ) + 1) * (j + 1 : ℝ)) /
                    flowPhi D x (j + 1) := by linarith
              have hydef : flowY D x (j + 2) =
                  x - ((D - (j + 1 : ℝ) + 1) * (j + 1 : ℝ)) /
                    flowY D x (j + 1) := by
                simp [flowY]
              rw [hydef]
              calc
                flowPhi D x (j + 2) ≤ flowPhi D x (j + 1) := hphiStep
                _ = x - ((D - (j + 1 : ℝ) + 1) * (j + 1 : ℝ)) /
                    flowPhi D x (j + 1) := by
                      convert hrec.symm using 1 <;> push_cast <;> ring
                _ ≤ x - ((D - (j + 1 : ℝ) + 1) * (j + 1 : ℝ)) /
                    flowY D x (j + 1) := hmain

private theorem flowP_one (M Q : ℕ) :
    flowP M Q 1 = ((M : ℝ) - Q) * flowP M Q 0 := by
  have hZ : p M Q ((M : ℤ) + Q - 1) =
      ((M : ℤ) - Q) * p M Q ((M : ℤ) + Q) := by
    rw [p_refl M Q 1, p_one M Q, p_top M Q]
    ring
  change ((p M Q ((M : ℤ) + Q - 1) : ℤ) : ℝ) =
    ((M : ℝ) - Q) * ((p M Q ((M : ℤ) + Q) : ℤ) : ℝ)
  exact_mod_cast hZ

private theorem flowP_step (M Q : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) + 1) * flowP M Q (n + 1) =
      ((M : ℝ) - Q) * flowP M Q n -
        ((M : ℝ) + Q - ((n - 1 : ℕ) : ℝ)) * flowP M Q (n - 1) := by
  let D : ℤ := (M : ℤ) + Q
  let x : ℤ := (M : ℤ) - Q
  have hrec := p_rec M Q (D - (n : ℤ))
  have hidx₁ : D - (n : ℤ) + 1 = D - ((n - 1 : ℕ) : ℤ) := by
    have hn' : (n : ℤ) = ((n - 1 : ℕ) : ℤ) + 1 := by omega
    omega
  have hidx₂ : D - (n : ℤ) - 1 = D - ((n + 1 : ℕ) : ℤ) := by omega
  have hcoef : D - (n : ℤ) - 1 - D = -((n : ℤ) + 1) := by ring
  rw [hcoef, hidx₁, hidx₂] at hrec
  have hZ : ((n : ℤ) + 1) * p M Q (D - ((n + 1 : ℕ) : ℤ)) =
      x * p M Q (D - (n : ℤ)) -
        (D - ((n - 1 : ℕ) : ℤ)) * p M Q (D - ((n - 1 : ℕ) : ℤ)) := by
    linear_combination hrec
  have hR : ((n : ℝ) + 1) * flowP M Q (n + 1) =
      ((M : ℝ) - Q) * flowP M Q n -
        ((M : ℝ) + Q - ((n - 1 : ℕ) : ℝ)) * flowP M Q (n - 1) := by
    have hR' : ((n : ℝ) + 1) *
          ((p M Q ((M : ℤ) + Q - ((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ) =
        ((M : ℝ) - Q) * ((p M Q ((M : ℤ) + Q - (n : ℤ)) : ℤ) : ℝ) -
          ((M : ℝ) + Q - ((n - 1 : ℕ) : ℝ)) *
            ((p M Q ((M : ℤ) + Q - ((n - 1 : ℕ) : ℤ)) : ℤ) : ℝ) := by
      dsimp [D, x] at hZ
      exact_mod_cast hZ
    simpa [flowP, Nat.cast_sub, hn] using hR'
  exact hR

private theorem flowP_ratio (M Q : ℕ) {K : ℕ}
    (hYpos : ∀ n, 1 ≤ n → n ≤ K →
      0 < flowY ((M : ℝ) + Q) ((M : ℝ) - Q) n) :
    ∀ n, 1 ≤ n → n ≤ K →
      flowY ((M : ℝ) + Q) ((M : ℝ) - Q) n * flowP M Q (n - 1) =
        (n : ℝ) * flowP M Q n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn hnK
      cases n with
      | zero => omega
      | succ m =>
          cases m with
          | zero =>
              simp [flowY, flowP_one]
          | succ j =>
              have hm : 1 ≤ j + 1 := by omega
              have hmK : j + 1 ≤ K := by omega
              have hprev := ih (j + 1) (by omega) hm hmK
              have hypos := hYpos (j + 1) hm hmK
              have hsub : (j + 1) - 1 = j := by omega
              have hprevEq : flowP M Q j =
                  ((j + 1 : ℝ) / flowY ((M : ℝ) + Q) ((M : ℝ) - Q) (j + 1)) *
                    flowP M Q (j + 1) := by
                have hyne :
                    flowY ((M : ℝ) + Q) ((M : ℝ) - Q) (j + 1) ≠ 0 :=
                  ne_of_gt hypos
                rw [hsub] at hprev
                field_simp [hyne]
                simpa [mul_comm, Nat.cast_succ] using hprev
              have hstep := flowP_step M Q (n := j + 1) hm
              rw [hsub] at hstep
              have hnat : j + 1 + 1 = j + 2 := by omega
              rw [hnat] at hstep
              have hstep' : ((j : ℝ) + 2) * flowP M Q (j + 2) =
                  ((M : ℝ) - Q) * flowP M Q (j + 1) -
                    ((M : ℝ) + Q - j) * flowP M Q j := by
                push_cast at hstep ⊢
                nlinarith [hstep]
              have hydef :
                  flowY ((M : ℝ) + Q) ((M : ℝ) - Q) (j + 2) =
                    ((M : ℝ) - Q) -
                      (((M : ℝ) + Q - j) * (j + 1 : ℝ)) /
                        flowY ((M : ℝ) + Q) ((M : ℝ) - Q) (j + 1) := by
                simp [flowY]
                ring
              have hcalc :
                  (((M : ℝ) - Q) -
                    (((M : ℝ) + Q - j) * (j + 1 : ℝ)) /
                      flowY ((M : ℝ) + Q) ((M : ℝ) - Q) (j + 1)) *
                    flowP M Q (j + 1) =
                      ((j : ℝ) + 2) * flowP M Q (j + 2) := by
                calc
                  _ = ((M : ℝ) - Q) * flowP M Q (j + 1) -
                        ((M : ℝ) + Q - j) * flowP M Q j := by
                    rw [hprevEq]
                    ring
                  _ = ((j : ℝ) + 2) * flowP M Q (j + 2) := hstep'.symm
              rw [hydef]
              have hsub2 : (j + 2) - 1 = j + 1 := by omega
              have hcast : (j : ℝ) + 2 = ((j + 1 : ℕ) : ℝ) + 1 := by
                push_cast
                ring
              rw [hcast] at hcalc
              simpa [hsub2, Nat.cast_add, Nat.cast_succ] using hcalc

set_option maxHeartbeats 1000000
/-- Theorem 3.3: on the flow region `(u+1)^2 ≥ (D+1)^2 - x^2` with `k = D - s ≥ 1`,
`T_s ≥ 0` (here `x = M - Q ≥ 0`). -/
theorem T_nonneg_flow (hQM : Q ≤ M) {s : ℤ} (hlo : (M : ℤ) + Q ≤ 2 * s)
    (hhi : s < (M : ℤ) + Q)
    (hf : ((M : ℤ) + Q + 1) ^ 2 - ((M : ℤ) - Q) ^ 2 ≤ (2 * s - ((M : ℤ) + Q) + 1) ^ 2) :
    0 ≤ T M Q s := by
  let dZ : ℤ := (M : ℤ) + Q
  let xZ : ℤ := (M : ℤ) - Q
  have hdge2 : 2 ≤ dZ := by dsimp [dZ]; omega
  have hxZnonneg : 0 ≤ xZ := by dsimp [xZ]; omega
  have hxZle : xZ ≤ dZ := by dsimp [xZ, dZ]; omega
  have hfD : (dZ + 1) ^ 2 - xZ ^ 2 ≤ (2 * s - dZ + 1) ^ 2 := by
    simpa [dZ, xZ] using hf
  have htopOffset : 1 ≤ 2 * s - dZ := by
    by_contra hnot
    have hu0 : 2 * s - dZ = 0 := by omega
    have hxSq : xZ ^ 2 ≤ dZ ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hxZle) (by omega : 0 ≤ dZ + xZ)
      nlinarith [hprod]
    rw [hu0] at hfD
    nlinarith [hxSq, hdge2]
  have hkZ : 1 ≤ dZ - s := by omega
  let K : ℕ := (dZ - s).toNat
  have hKcast : (K : ℤ) = dZ - s := by
    dsimp [K]
    exact Int.toNat_of_nonneg (by omega)
  have hKpos : 1 ≤ K := by omega
  have hKtopZ : 1 ≤ dZ - 2 * (K : ℤ) := by
    rw [hKcast]
    omega
  have hiden : 4 * (dZ - s) * (dZ + 1 - (dZ - s)) =
      (dZ + 1) ^ 2 - (2 * s - dZ + 1) ^ 2 := by ring
  have hRadZ : 0 ≤ xZ ^ 2 - 4 * (K : ℤ) * (dZ + 1 - (K : ℤ)) := by
    rw [hKcast]
    nlinarith [hfD, hiden]
  have hRadDS : 0 ≤ xZ ^ 2 - 4 * (dZ - s) * (s + 1) := by
    have h := hRadZ
    rw [hKcast, show dZ + 1 - (dZ - s) = s + 1 by ring] at h
    exact h
  have hxZpos : 0 < xZ := by
    by_contra hnot
    have hx0 : xZ = 0 := by omega
    have hprod := mul_pos (show 0 < dZ - s by omega) (show 0 < s + 1 by omega)
    rw [hx0] at hRadDS
    nlinarith [hprod]
  have hKtopR : 1 ≤ (M : ℝ) + Q - 2 * (K : ℝ) := by
    have h := hKtopZ
    dsimp [dZ] at h
    exact_mod_cast h
  have hxR : 0 < (M : ℝ) - Q := by
    have h := hxZpos
    dsimp [xZ] at h
    exact_mod_cast h
  have hRadR : 0 ≤ flowRad ((M : ℝ) + Q) ((M : ℝ) - Q) K := by
    change 0 ≤ ((M : ℝ) - Q) ^ 2 -
      4 * (K : ℝ) * ((M : ℝ) + Q + 1 - (K : ℝ))
    have h := hRadZ
    dsimp [dZ, xZ] at h
    exact_mod_cast h
  have hYbound := flowY_bound (D := (M : ℝ) + Q) (x := (M : ℝ) - Q)
    (K := K) hKtopR hRadR hxR
  have hYpos : ∀ n, 1 ≤ n → n ≤ K →
      0 < flowY ((M : ℝ) + Q) ((M : ℝ) - Q) n := by
    intro n hn hnK
    exact lt_of_lt_of_le
      (flowPhi_chain (n := n) (K := K) hKtopR hRadR hxR hn hnK)
      (hYbound n hn hnK)
  have hRatio := flowP_ratio M Q (K := K) hYpos
  have hKcast' : (K : ℤ) = (M : ℤ) + Q - s := by
    simpa [dZ] using hKcast
  have hidxK : (M : ℤ) + Q - (K : ℤ) = s := by omega
  have hKsub : ((K - 1 : ℕ) : ℤ) + 1 = (K : ℤ) := by
    exact_mod_cast (Nat.sub_add_cancel hKpos)
  have hidxKm1 : (M : ℤ) + Q - ((K - 1 : ℕ) : ℤ) = s + 1 := by omega
  have hPK : flowP M Q K = (p M Q s : ℝ) := by
    simp [flowP, hidxK]
  have hPKm1 : flowP M Q (K - 1) = (p M Q (s + 1) : ℝ) := by
    simp [flowP, hidxKm1]
  have htopNZ : flowP M Q 0 ≠ 0 := by
    have hpow : ((-1 : ℝ) ^ Q) ≠ 0 := pow_ne_zero Q (by norm_num)
    simpa [flowP, p_top] using hpow
  have hPNZ : ∀ n, n ≤ K → flowP M Q n ≠ 0 := by
    intro n
    induction n with
    | zero =>
        intro _
        exact htopNZ
    | succ n ih =>
        intro hn
        have hn1 : 1 ≤ n + 1 := by omega
        have hrr : flowY ((M : ℝ) + Q) ((M : ℝ) - Q) (n + 1) *
              flowP M Q n = ((n : ℝ) + 1) * flowP M Q (n + 1) := by
          simpa using hRatio (n + 1) hn1 (by omega)
        have hy : 0 < flowY ((M : ℝ) + Q) ((M : ℝ) - Q) (n + 1) :=
          hYpos (n + 1) hn1 (by omega)
        have hmulne := mul_ne_zero (ne_of_gt hy) (ih (by omega))
        intro hzero
        apply hmulne
        rw [hrr, hzero]
        simp
  let a : ℝ := (p M Q s : ℝ)
  let b : ℝ := (p M Q (s + 1) : ℝ)
  have ha : a ≠ 0 := by
    have h := hPNZ K le_rfl
    rw [hPK] at h
    exact h
  have hratioK : flowY ((M : ℝ) + Q) ((M : ℝ) - Q) K * b =
      (K : ℝ) * a := by
    have h := hRatio K hKpos le_rfl
    rw [hPKm1, hPK] at h
    exact h
  let d : ℝ := (M : ℝ) + Q
  let x : ℝ := (M : ℝ) - Q
  let k : ℝ := (K : ℝ)
  let sr : ℝ := d - k
  let u : ℝ := d - 2 * k
  let phi : ℝ := flowPhi d x K
  let w : ℝ := Real.sqrt (flowRad d x K)
  let quadA : ℝ := u + 2
  let quadB : ℝ := x * (u + 1)
  let quadC : ℝ := u * (sr + 2)
  have hkR : 1 ≤ k := by
    change 1 ≤ (K : ℝ)
    exact_mod_cast hKpos
  have hphiPos : 0 < phi := by
    exact flowPhi_chain (n := K) (K := K) hKtopR hRadR hxR hKpos le_rfl
  have hyPos : 0 < flowY d x K := hYpos K hKpos le_rfl
  have hYle : phi ≤ flowY d x K := hYbound K hKpos le_rfl
  have hRadR' : 0 ≤ x ^ 2 - 4 * k * (d + 1 - k) := by
    simpa [flowRad, d, x, k] using hRadR
  have hw0 : 0 ≤ w := by dsimp [w]; exact Real.sqrt_nonneg _
  have hwSq : w ^ 2 = x ^ 2 - 4 * k * (d + 1 - k) := by
    dsimp [w]
    exact Real.sq_sqrt hRadR'
  have hI1 : 0 ≤ flowI1 d x k w :=
    flowI1_nonneg hxR.le hkR hKtopR hRadR' hwSq hw0
  have hI2 : 0 ≤ flowI2 d x k w :=
    flowI2_nonneg hxR.le hkR hKtopR hRadR' hwSq hw0
  have hphiDef : phi = (x + w) / 2 := by
    simp [phi, w, flowPhi]
  have hI1' :
      0 ≤ quadA * (k + 1) * phi ^ 2 - quadB * k * phi + quadC * k ^ 2 := by
    simpa [flowI1, flowPhi, phi, w, quadA, quadB, quadC, u, sr] using hI1
  have hI2' : 0 ≤ quadB * phi - 2 * quadC * k := by
    have h := hI2
    dsimp [flowI2, flowPhi, phi, w, quadB, quadC, u, sr] at h ⊢
    nlinarith [h]
  let yk : ℝ := flowY d x K
  let r : ℝ := k / yk
  let z : ℝ := k / phi
  let F : ℝ → ℝ := fun t => quadA * (k + 1) - quadB * t + quadC * t ^ 2
  have hyne : yk ≠ 0 := ne_of_gt hyPos
  have hbr : b = r * a := by
    dsimp [r, yk, k]
    field_simp [ne_of_gt hyPos]
    nlinarith [hratioK]
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (by positivity) (le_of_lt hyPos)
  have hz0 : 0 ≤ z := by
    dsimp [z]
    exact div_nonneg (by positivity) (le_of_lt hphiPos)
  have hrz : r ≤ z := by
    dsimp [r, z, yk]
    rw [div_le_div_iff₀ hyPos hphiPos]
    exact mul_le_mul_of_nonneg_left hYle (by positivity)
  have hphi2 : phi ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hphiPos)
  have hFzId : F z * phi ^ 2 =
      quadA * (k + 1) * phi ^ 2 - quadB * k * phi + quadC * k ^ 2 := by
    dsimp [F, z]
    field_simp [ne_of_gt hphiPos]
  have hFzEq : F z =
      (quadA * (k + 1) * phi ^ 2 - quadB * k * phi + quadC * k ^ 2) / phi ^ 2 := by
    apply (eq_div_iff hphi2).2
    exact hFzId
  have hFz : 0 ≤ F z := by
    rw [hFzEq]
    exact div_nonneg hI1' (sq_nonneg phi)
  have hvertex : 2 * quadC * z ≤ quadB := by
    have hmul : 2 * quadC * k ≤ quadB * phi := by linarith [hI2']
    rw [show 2 * quadC * z = (2 * quadC * k) / phi by dsimp [z]; ring]
    exact (div_le_iff₀ hphiPos).2 hmul
  have hCnonneg : 0 ≤ quadC := by
    have hsr : 0 < sr + 2 := by dsimp [sr, u]; nlinarith [hKtopR, hkR]
    dsimp [quadC, u]
    exact mul_nonneg (by linarith [hKtopR]) (le_of_lt hsr)
  have hsum : z + r ≤ 2 * z := by linarith [hrz]
  have hmul := mul_le_mul_of_nonneg_left hsum hCnonneg
  have hmono : 0 ≤ quadB - quadC * (z + r) := by nlinarith [hvertex, hmul]
  have hdiff : F r - F z = (z - r) * (quadB - quadC * (z + r)) := by
    dsimp [F]
    ring
  have hFr : 0 ≤ F r := by
    have hprod := mul_nonneg (sub_nonneg.mpr hrz) hmono
    nlinarith [hdiff, hFz]
  have hqReal :
      ((s : ℝ) + 2) * (((M : ℝ) + Q + 1) - (s : ℝ)) *
          (T M Q s : ℝ) =
        (2 * (s : ℝ) - ((M : ℝ) + Q) + 2) *
            (((M : ℝ) + Q + 1) - (s : ℝ)) * a ^ 2 -
          ((M : ℝ) - Q) * (2 * (s : ℝ) - ((M : ℝ) + Q) + 1) * a * b +
          (2 * (s : ℝ) - ((M : ℝ) + Q)) * ((s : ℝ) + 2) * b ^ 2 := by
    dsimp [a, b]
    exact_mod_cast qform M Q s
  have hKrealEq : k = d - (s : ℝ) := by
    dsimp [k, d]
    exact_mod_cast hKcast'
  have hsr : sr = (s : ℝ) := by dsimp [sr]; linarith [hKrealEq]
  have hu : u = 2 * (s : ℝ) - d := by dsimp [u]; linarith [hKrealEq]
  have hDtop : d + 1 - (s : ℝ) = k + 1 := by linarith [hKrealEq]
  have hDsr : d - sr = k := by
    rw [hsr]
    exact hKrealEq.symm
  have hDtop' : (M : ℝ) + Q + 1 - sr = k + 1 := by
    calc
      (M : ℝ) + Q + 1 - sr = (d - sr) + 1 := by dsimp [d]; ring
      _ = k + 1 := by rw [hDsr]
  have hu' : u = 2 * sr - ((M : ℝ) + Q) := by
    calc
      u = d - 2 * k := rfl
      _ = d - 2 * (d - sr) := by rw [← hDsr]
      _ = 2 * sr - d := by ring
      _ = 2 * sr - ((M : ℝ) + Q) := by rfl
  have hqScaled :
      (sr + 2) * (k + 1) * (T M Q s : ℝ) = a ^ 2 * F r := by
    rw [← hsr, hDtop', ← hu'] at hqReal
    rw [hbr] at hqReal
    calc
      _ = (u + 2) * (k + 1) * a ^ 2 -
            ((M : ℝ) - Q) * (u + 1) * a * (r * a) +
            u * (sr + 2) * (r * a) ^ 2 := by
        simpa [quadA, quadB, quadC] using hqReal
      _ = a ^ 2 * F r := by
        dsimp [F, quadA, quadB, quadC, x]
        ring
  have hscaled : 0 ≤ (sr + 2) * (k + 1) * (T M Q s : ℝ) := by
    rw [hqScaled]
    exact mul_nonneg (sq_nonneg a) hFr
  have hden : 0 < (sr + 2) * (k + 1) := by
    have hsr2Eq : sr + 2 = u + k + 2 := by dsimp [sr, u]; ring
    have huPos : 0 < u := by linarith [hKtopR]
    have hkPos : 0 < k := by linarith [hkR]
    have hsr2 : 0 < sr + 2 := by rw [hsr2Eq]; linarith
    exact mul_pos hsr2 (by linarith [hkPos])
  by_contra hT
  have hTneg : (T M Q s : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hT)
  have hstrict : (sr + 2) * (k + 1) * (T M Q s : ℝ) < 0 := by
    simpa using mul_lt_mul_of_pos_left hTneg hden
  exact (not_lt_of_ge hscaled) hstrict

end Kraw
