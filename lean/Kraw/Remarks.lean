import Kraw.Main

/-!
# Remaining statements of paper §§1–3
-/

open Matrix
open Polynomial

namespace Kraw

private theorem remarks_Tur_antitone_interval (M Q : ℕ) {a b : ℤ}
    (hA : (M : ℤ) + Q ≤ 2 * a) (hab : a ≤ b) (hb : b ≤ (M : ℤ) + Q) :
    Tur M Q b ≤ Tur M Q a := by
  have haux : ∀ n : ℕ, (n : ℤ) ≤ b - a → Tur M Q (a + n) ≤ Tur M Q a := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hnle : (n : ℤ) ≤ b - a := by omega
      have hidx : a + (n : ℤ) ≤ b := by omega
      have hstep := Tur_antitone_top M Q (s := a + (n : ℤ)) (by omega) (by omega)
      have hcast : a + ((n + 1 : ℕ) : ℤ) = (a + (n : ℤ)) + 1 := by push_cast; ring
      rw [hcast]
      exact le_trans hstep (ih hnle)
  have hdiff : 0 ≤ b - a := by omega
  have hnat : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg hdiff
  have h := haux (b - a).toNat (by rw [hnat])
  rw [hnat] at h
  have hidx : a + (b - a) = b := by omega
  rw [hidx] at h
  exact h

private theorem remarks_Tur_zero_above (M Q : ℕ) {r : ℤ}
    (hr : (M : ℤ) + Q < r) : Tur M Q r = 0 := by
  have hr1 : (M : ℤ) + Q < r + 1 := by omega
  unfold Tur
  rw [p_of_gt M Q hr, p_of_gt M Q hr1]
  simp

/-- §1.1: `Tur` is non-decreasing on the bottom half (`0 ≤ s ≤ t ≤ ⌈D/2⌉`). -/
theorem Tur_monotone_left (M Q : ℕ) {s t : ℤ} (h0 : 0 ≤ s) (hst : s ≤ t)
    (ht : 2 * t ≤ (M : ℤ) + Q + 1) : Tur M Q s ≤ Tur M Q t := by
  let D : ℤ := (M : ℤ) + Q
  by_cases hmid : 2 * t ≤ D
  · have htop : Tur M Q (D - s) ≤ Tur M Q (D - t) :=
      remarks_Tur_antitone_interval M Q (a := D - t) (b := D - s)
        (by dsimp [D]; omega) (by omega) (by dsimp [D]; omega)
    calc
      Tur M Q s = Tur M Q (D - s) := (Tur_refl M Q s).symm
      _ ≤ Tur M Q (D - t) := htop
      _ = Tur M Q t := Tur_refl M Q t
  · have hedge : 2 * t = D + 1 := by dsimp [D] at *; omega
    by_cases heq : s = t
    · simp [heq]
    · have hstlt : s < t := by omega
      have htop : Tur M Q (D - s) ≤ Tur M Q t := by
        exact remarks_Tur_antitone_interval M Q (a := t) (b := D - s)
          (by rw [hedge]; dsimp [D]; omega)
          (by dsimp [D]; omega) (by dsimp [D]; omega)
      calc
        Tur M Q s = Tur M Q (D - s) := (Tur_refl M Q s).symm
        _ ≤ Tur M Q t := htop

/-- §1.1: `Tur` is non-increasing on the top half. -/
theorem Tur_antitone_right (M Q : ℕ) {s t : ℤ} (hs : (M : ℤ) + Q ≤ 2 * s) (hst : s ≤ t) :
    Tur M Q t ≤ Tur M Q s := by
  by_cases hsD : s ≤ (M : ℤ) + Q
  · by_cases htD : t ≤ (M : ℤ) + Q
    · exact remarks_Tur_antitone_interval M Q hs hst htD
    · have htgt : (M : ℤ) + Q < t := by omega
      rw [remarks_Tur_zero_above M Q htgt]
      have hs0 : 0 ≤ s := by omega
      have hpos : 1 ≤ Tur M Q s := Tur_ge_one M Q hs0 hsD
      omega
  · have hsgt : (M : ℤ) + Q < s := by omega
    have htgt : (M : ℤ) + Q < t := by omega
    rw [remarks_Tur_zero_above M Q htgt, remarks_Tur_zero_above M Q hsgt]

private theorem remarks_p_nat_eq (M Q : ℕ) (n : ℕ) :
    p M Q (n : ℤ) = (gen M Q).coeff n := by
  simp [p]

private theorem remarks_neg_X_pow (n : ℕ) :
    (-X : ℤ[X]) ^ n = C ((-1 : ℤ) ^ n) * X ^ n := by
  calc
    (-X : ℤ[X]) ^ n = (C (-1) * X) ^ n := by congr 1 <;> simp
    _ = C (-1) ^ n * X ^ n := mul_pow _ _ _
    _ = C ((-1 : ℤ) ^ n) * X ^ n := by simp

private theorem remarks_coeff_comp_neg (f : ℤ[X]) (n : ℕ) :
    (f.comp (-X)).coeff n = (-1 : ℤ) ^ n * f.coeff n := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]; ring
  | monomial k a =>
    have hpoly : C a * (-X : ℤ[X]) ^ k = C (a * (-1 : ℤ) ^ k) * X ^ k := by
      rw [remarks_neg_X_pow]
      calc
        C a * (C ((-1 : ℤ) ^ k) * X ^ k) =
            (C a * C ((-1 : ℤ) ^ k)) * X ^ k := by ring
        _ = C (a * (-1 : ℤ) ^ k) * X ^ k := by rw [← Polynomial.C_mul]
    by_cases h : k = n
    · subst n
      rw [Polynomial.monomial_comp, hpoly]
      rw [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_monomial]
      simp
      ring
    · rw [Polynomial.monomial_comp, hpoly]
      rw [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_monomial]
      have hn : n ≠ k := fun hnk => h hnk.symm
      simp [h, hn]

private theorem remarks_gen_swap_poly (M Q : ℕ) :
    gen Q M = (gen M Q).comp (-X) := by
  unfold gen
  simp [Polynomial.comp, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  ring

private theorem remarks_p_swap_nat (M Q : ℕ) (n : ℕ) :
    p Q M (n : ℤ) = (-1 : ℤ) ^ n * p M Q (n : ℤ) := by
  have h := congrArg (fun f : ℤ[X] => f.coeff n) (remarks_gen_swap_poly M Q)
  rw [remarks_coeff_comp_neg] at h
  calc
    p Q M (n : ℤ) = (gen Q M).coeff n := remarks_p_nat_eq Q M n
    _ = (-1 : ℤ) ^ n * (gen M Q).coeff n := h
    _ = (-1 : ℤ) ^ n * p M Q (n : ℤ) := by rw [← remarks_p_nat_eq M Q n]

/-- §1.4: `w ↦ -w` sends `p_s` to `(-1)^s p_s` and swaps the exponents. -/
theorem p_swap (M Q : ℕ) {s : ℤ} (hs : 0 ≤ s) : p Q M s = (-1) ^ s.toNat * p M Q s := by
  have h := remarks_p_swap_nat M Q s.toNat
  have hs' : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs
  simpa [hs'] using h

/-- §2: the top initial value `p_{D-1} = (-1)^Q x`. -/
theorem p_top_sub_one (M Q : ℕ) :
    p M Q ((M : ℤ) + Q - 1) = (-1) ^ Q * ((M : ℤ) - Q) := by
  rw [p_refl M Q 1, p_one]

/-- Theorem 3.1, (3.1): `T_s = A p_s² + B p_s p_{s+1} + C p_{s+1}²`. -/
theorem quadForm_rational (M Q : ℕ) (s : ℤ) (h1 : (s : ℚ) + 2 ≠ 0)
    (h2 : (M : ℚ) + Q + 1 - s ≠ 0) :
    (T M Q s : ℚ) =
      (2 * s - ((M : ℚ) + Q) + 2) / (s + 2) * (p M Q s : ℚ) ^ 2 +
        -((M : ℚ) - Q) * (2 * s - ((M : ℚ) + Q) + 1) / (((M : ℚ) + Q + 1 - s) * (s + 2)) *
          (p M Q s : ℚ) * (p M Q (s + 1) : ℚ) +
        (2 * s - ((M : ℚ) + Q)) / ((M : ℚ) + Q + 1 - s) * (p M Q (s + 1) : ℚ) ^ 2 := by
  have hq := congrArg (fun z : ℤ => (z : ℚ)) (qform M Q s)
  push_cast at hq
  field_simp [h1, h2]
  nlinarith [hq]

/-- Theorem 3.1, (3.2): the negated discriminant. -/
theorem disc_rational (D x s : ℚ) (h1 : s + 2 ≠ 0) (h2 : D + 1 - s ≠ 0) :
    4 * ((2 * s - D + 2) / (s + 2)) * ((2 * s - D) / (D + 1 - s)) -
        (-x * (2 * s - D + 1) / ((D + 1 - s) * (s + 2))) ^ 2 =
      ((2 * s - D) * (2 * s - D + 2) * ((D + 3) ^ 2 - (2 * s - D + 1) ^ 2) -
          x ^ 2 * (2 * s - D + 1) ^ 2) / ((D + 1 - s) * (s + 2)) ^ 2 := by
  field_simp [h1, h2]
  ring

/-- The recurrence step `(p_{k-1}, p_k) ↦ (p_k, p_{k+1})`. -/
noncomputable def stepMat (D x k : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, 1; (k - 1 - D) / (k + 1), x / (k + 1)]

/-- The symmetric matrix of the binary quadratic form `A a² + B a b + C b²`. -/
noncomputable def formMat (A B C : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := !![A, B / 2; B / 2, C]

theorem stepMat_spec (M Q : ℕ) (k : ℤ) (hk : (k : ℚ) + 1 ≠ 0) :
    (![(p M Q k : ℚ), p M Q (k + 1)] : Fin 2 → ℚ) =
      stepMat ((M : ℚ) + Q) ((M : ℚ) - Q) k *ᵥ ![(p M Q (k - 1) : ℚ), p M Q k] := by
  have hrec : ((k : ℚ) + 1) * (p M Q (k + 1) : ℚ) =
      ((M : ℚ) - Q) * (p M Q k : ℚ) + (k - 1 - ((M : ℚ) + Q)) * (p M Q (k - 1) : ℚ) := by
    exact_mod_cast p_rec M Q k
  ext i
  fin_cases i
  · simp [stepMat, Matrix.mulVec, dotProduct]
  · simp [stepMat, Matrix.mulVec, dotProduct]
    field_simp [hk]
    nlinarith [hrec]

theorem stepMat_det (D x k : ℚ) (hk : k + 1 ≠ 0) :
    (stepMat D x k).det = (D + 1 - k) / (k + 1) := by
  simp [stepMat, Matrix.det_fin_two]
  field_simp [hk]
  ring

private theorem remarks_quadratic_congr {α : Type} [CommSemiring α]
    (F R : Matrix (Fin 2) (Fin 2) α) (w : Fin 2 → α) :
    w ⬝ᵥ ((R.transpose * F * R) *ᵥ w) =
      (R *ᵥ w) ⬝ᵥ (F *ᵥ (R *ᵥ w)) := by
  calc
    w ⬝ᵥ ((R.transpose * F * R) *ᵥ w) =
        w ⬝ᵥ (R.transpose *ᵥ (F *ᵥ (R *ᵥ w))) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = (R *ᵥ w) ⬝ᵥ (F *ᵥ (R *ᵥ w)) := by
      rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

/-- Remark after Theorem 3.1: in the basis `(p_{s-2}, p_{s-1})` the form of `T_s` is
`Rᵀ F R`, and its determinant (a quarter of the negated discriminant) is multiplied by
`((D+1-s)(D+2-s)/(s(s+1)))²`. -/
theorem shift_two_basis (M Q : ℕ) (s : ℤ) (hs : 1 ≤ s) (hsD : s ≤ (M : ℤ) + Q) :
    let D : ℚ := M + Q
    let x : ℚ := M - Q
    let u : ℚ := 2 * s - D
    let F := formMat ((u + 2) / (s + 2)) (-x * (u + 1) / ((D + 1 - s) * (s + 2))) (u / (D + 1 - s))
    let R := stepMat D x s * stepMat D x (s - 1)
    let w : Fin 2 → ℚ := ![(p M Q (s - 2) : ℚ), p M Q (s - 1)]
    (T M Q s : ℚ) = w ⬝ᵥ ((R.transpose * F * R) *ᵥ w) ∧
      (R.transpose * F * R).det = F.det * (((D + 1 - s) * (D + 2 - s)) / (s * (s + 1))) ^ 2 := by
  let D : ℚ := (M : ℚ) + Q
  let x : ℚ := (M : ℚ) - Q
  let u : ℚ := 2 * (s : ℚ) - D
  let F := formMat ((u + 2) / (s + 2)) (-x * (u + 1) / ((D + 1 - s) * (s + 2)))
    (u / (D + 1 - s))
  let R := stepMat D x s * stepMat D x (s - 1)
  let w : Fin 2 → ℚ := ![(p M Q (s - 2) : ℚ), p M Q (s - 1)]
  let v : Fin 2 → ℚ := ![(p M Q s : ℚ), p M Q (s + 1)]
  have hsQ : (s : ℚ) + 2 ≠ 0 := by positivity
  have hspos : 0 < (s : ℚ) := by exact_mod_cast (show 0 < s by omega)
  have hs0 : (s : ℚ) ≠ 0 := ne_of_gt hspos
  have hs1 : (s : ℚ) + 1 ≠ 0 := by positivity
  have hstepPrev := stepMat_spec M Q (s - 1) (by
    have h : s - 1 + 1 ≠ 0 := by omega
    exact_mod_cast h)
  have hstepCurr := stepMat_spec M Q s (by positivity)
  have hprev : ![(p M Q (s - 1) : ℚ), p M Q s] =
      stepMat D x (s - 1) *ᵥ w := by
    have hidx : s - 1 - 1 = s - 2 := by omega
    simpa [D, x, w, hidx] using hstepPrev
  have hcurr : v = stepMat D x s *ᵥ ![(p M Q (s - 1) : ℚ), p M Q s] := by
    simpa [D, x, v] using hstepCurr
  have hRvec : R *ᵥ w = v := by
    change (stepMat D x s * stepMat D x (s - 1)) *ᵥ w = v
    calc
      (stepMat D x s * stepMat D x (s - 1)) *ᵥ w =
          stepMat D x s *ᵥ (stepMat D x (s - 1) *ᵥ w) := by
            rw [← Matrix.mulVec_mulVec]
      _ = stepMat D x s *ᵥ ![(p M Q (s - 1) : ℚ), p M Q s] := by rw [← hprev]
      _ = v := hcurr.symm
  have hquad := quadForm_rational M Q s hsQ (by
    have hsDq : (s : ℚ) ≤ (M : ℚ) + Q := by exact_mod_cast hsD
    have hposq : 0 < (M : ℚ) + Q + 1 - s := by linarith
    exact ne_of_gt hposq)
  have hform : v ⬝ᵥ (F *ᵥ v) =
      (2 * (s : ℚ) - ((M : ℚ) + Q) + 2) / (s + 2) * (p M Q s : ℚ) ^ 2 +
        -((M : ℚ) - Q) * (2 * (s : ℚ) - ((M : ℚ) + Q) + 1) /
          (((M : ℚ) + Q + 1 - s) * (s + 2)) *
          (p M Q s : ℚ) * (p M Q (s + 1) : ℚ) +
        (2 * (s : ℚ) - ((M : ℚ) + Q)) / ((M : ℚ) + Q + 1 - s) *
          (p M Q (s + 1) : ℚ) ^ 2 := by
    simp [F, v, D, x, u, formMat, Matrix.mulVec, dotProduct]
    ring
  constructor
  · calc
      (T M Q s : ℚ) =
          (2 * (s : ℚ) - ((M : ℚ) + Q) + 2) / (s + 2) * (p M Q s : ℚ) ^ 2 +
            -((M : ℚ) - Q) * (2 * (s : ℚ) - ((M : ℚ) + Q) + 1) /
              (((M : ℚ) + Q + 1 - s) * (s + 2)) *
              (p M Q s : ℚ) * (p M Q (s + 1) : ℚ) +
            (2 * (s : ℚ) - ((M : ℚ) + Q)) / ((M : ℚ) + Q + 1 - s) *
              (p M Q (s + 1) : ℚ) ^ 2 := hquad
      _ = v ⬝ᵥ (F *ᵥ v) := hform.symm
      _ = (R *ᵥ w) ⬝ᵥ (F *ᵥ (R *ᵥ w)) := by rw [← hRvec]
      _ = w ⬝ᵥ ((R.transpose * F * R) *ᵥ w) :=
        (remarks_quadratic_congr F R w).symm
  · have hdetS : (stepMat D x s).det = (D + 1 - s) / (s + 1) :=
      stepMat_det D x s (by positivity)
    have hdetPrev : (stepMat D x (s - 1)).det = (D + 2 - s) / s := by
      rw [stepMat_det D x (s - 1) (by
        have h : (s : ℚ) ≠ 0 := hs0
        convert h using 1 <;> ring)]
      congr 1 <;> ring
    have hdetR : R.det = ((D + 1 - s) * (D + 2 - s)) / (s * (s + 1)) := by
      change (stepMat D x s * stepMat D x (s - 1)).det = _
      rw [Matrix.det_mul, hdetS, hdetPrev]
      field_simp [hs0, hs1] <;> ring
    have hdetCong : (R.transpose * F * R).det =
        F.det * (((D + 1 - s) * (D + 2 - s)) / (s * (s + 1))) ^ 2 := by
      change ((R.transpose * F) * R).det = _
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetR]
      ring
    exact hdetCong

/-- Remark after Theorem 3.1: an invertible change of basis does not change positive
semidefiniteness, so no shifted basis enlarges the bulk band. -/
theorem psd_congr (F R : Matrix (Fin 2) (Fin 2) ℝ) (hR : R.det ≠ 0) :
    (∀ v : Fin 2 → ℝ, 0 ≤ v ⬝ᵥ (F *ᵥ v)) ↔
      ∀ w : Fin 2 → ℝ, 0 ≤ w ⬝ᵥ ((R.transpose * F * R) *ᵥ w) := by
  have hdetUnit : IsUnit R.det := isUnit_iff_ne_zero.mpr hR
  have hRUnit : IsUnit R := R.isUnit_iff_isUnit_det.mpr hdetUnit
  have hsurj : Function.Surjective R.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hRUnit
  constructor
  · intro h w
    rw [remarks_quadratic_congr]
    exact h (R *ᵥ w)
  · intro h v
    obtain ⟨w, hw⟩ := hsurj v
    have hq := h w
    rw [remarks_quadratic_congr, hw] at hq
    exact hq

/-- Theorem 3.2, odd `Q`. -/
theorem center_odd (M Q : ℕ) (hQ : Odd Q) {s : ℤ} (hs : 2 * s = (M : ℤ) + Q) :
    p M Q s = 0 ∧ T M Q s = 0 := by
  have r0 := p_refl M Q s
  have r1 := p_refl M Q (s + 1)
  have e0 : (M : ℤ) + Q - s = s := by omega
  have e1 : (M : ℤ) + Q - (s + 1) = s - 1 := by omega
  rw [e0] at r0
  rw [e1] at r1
  rw [hQ.neg_one_pow] at r0 r1
  have hps : p M Q s = 0 := by linarith
  constructor
  · exact hps
  · have hT : T M Q s = 0 := by
      unfold T Tur
      have e : s + 1 - 1 = s := by ring
      rw [e, hps]
      rw [r1]
      ring
    exact hT

/-- Theorem 3.2, even `Q`: the rank-one relation and (3.4). -/
theorem center_even (M Q : ℕ) (hQ : Even Q) {s : ℤ} (hs : 2 * s = (M : ℤ) + Q) :
    ((M : ℤ) + Q + 2) * p M Q (s + 1) = ((M : ℤ) - Q) * p M Q s ∧
      ((M : ℤ) + Q + 2) ^ 2 * ((M : ℤ) + Q + 4) * T M Q s =
        4 * p M Q s ^ 2 * (((M : ℤ) + Q + 2) ^ 2 - ((M : ℤ) - Q) ^ 2) ∧
      0 < T M Q s := by
  let D : ℤ := (M : ℤ) + Q
  let x : ℤ := (M : ℤ) - Q
  have r1 := p_refl M Q (s + 1)
  have e1 : D - (s + 1) = s - 1 := by dsimp [D]; omega
  rw [e1, hQ.neg_one_pow, one_mul] at r1
  have hrec := p_rec M Q s
  rw [r1] at hrec
  have hrel : (D + 2) * p M Q (s + 1) = x * p M Q s := by
    dsimp [D, x]
    linarith [hrec]
  have hq := qform M Q s
  have hu0 : 2 * s - D = 0 := by dsimp [D]; omega
  rw [hu0] at hq
  have e2 : D + 1 - s = s + 1 := by dsimp [D]; omega
  have hq' := hq
  rw [e2] at hq'
  have hq'' : (s + 2) * (s + 1) * T M Q s =
      2 * (s + 1) * p M Q s ^ 2 - x * p M Q s * p M Q (s + 1) := by
    simpa [x] using hq'
  have hDplus : D + 2 = 2 * (s + 1) := by dsimp [D]; omega
  have hkey : (D + 2) * ((s + 2) * (D + 1 - s) * T M Q s) =
      ((D + 2) ^ 2 - x ^ 2) * p M Q s ^ 2 := by
    calc
      (D + 2) * ((s + 2) * (D + 1 - s) * T M Q s) =
          2 * (s + 1) * ((s + 2) * (s + 1) * T M Q s) := by rw [hDplus, e2]
      _ = 2 * (s + 1) *
          (2 * (s + 1) * p M Q s ^ 2 - x * p M Q s * p M Q (s + 1)) := by
            rw [hq'']
      _ = ((D + 2) ^ 2 - x ^ 2) * p M Q s ^ 2 := by
            rw [hDplus]
            have hrel' : 2 * (s + 1) * p M Q (s + 1) = x * p M Q s := by
              rw [← hDplus]
              exact hrel
            linear_combination (-x * p M Q s) * hrel'
  have hformula : (D + 2) ^ 2 * (D + 4) * T M Q s =
      4 * p M Q s ^ 2 * ((D + 2) ^ 2 - x ^ 2) := by
    have hkey' := hkey
    rw [hDplus, e2] at hkey'
    have hDplus4 : D + 4 = 2 * (s + 2) := by dsimp [D]; omega
    rw [hDplus, hDplus4]
    linear_combination 4 * hkey'
  have hp : p M Q s ≠ 0 := by
    intro hzero
    have hnextmul : (D + 2) * p M Q (s + 1) = 0 := by
      rw [hzero] at hrel
      simpa using hrel
    have hnext : p M Q (s + 1) = 0 := by
      rcases mul_eq_zero.mp hnextmul with h | h
      · have : D + 2 ≠ 0 := by dsimp [D]; omega
        exact (this h).elim
      · exact h
    have hs0 : 0 ≤ s := by omega
    have hsD : s ≤ (M : ℤ) + Q := by omega
    exact (no_consec_zero M Q hs0 hsD) ⟨hzero, hnext⟩
  have hfac : 0 < (D + 2) ^ 2 - x ^ 2 := by
    have hfacid : (D + 2) ^ 2 - x ^ 2 =
        4 * ((M : ℤ) + 1) * ((Q : ℤ) + 1) := by
      dsimp [D, x]
      push_cast
      ring
    rw [hfacid]
    positivity
  have hp2 : 0 < p M Q s ^ 2 := sq_pos_of_ne_zero hp
  have hcoef : 0 < (D + 2) ^ 2 * (D + 4) := by dsimp [D]; positivity
  have hprod : 0 < ((D + 2) ^ 2 * (D + 4)) * T M Q s := by
    rw [hformula]
    exact mul_pos (mul_pos (by norm_num) hp2) hfac
  have hTpos : 0 < T M Q s := by
    by_contra hT
    have hnonpos : T M Q s ≤ 0 := le_of_not_gt hT
    have hle := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hcoef) hnonpos
    linarith
  refine ⟨?_, ?_, hTpos⟩
  · simpa [D, x] using hrel
  · simpa [D, x] using hformula

/-- §3.2: `T_{D/2} = 0` exactly when `M` and `Q` are both odd. -/
theorem T_center_eq_zero_iff (M Q : ℕ) {s : ℤ} (hs : 2 * s = (M : ℤ) + Q) :
    T M Q s = 0 ↔ Odd M ∧ Odd Q := by
  constructor
  · intro hT
    rcases Nat.even_or_odd Q with hQ | hQ
    · rcases Nat.even_or_odd M with hM | hM
      · have hpos := (center_even M Q hQ hs).2.2
        exact False.elim ((ne_of_gt hpos) hT)
      · rcases hM with ⟨m, hm⟩
        rcases hQ with ⟨q, hq⟩
        omega
    · have hM : Odd M := by
        rcases Nat.even_or_odd M with hM | hM
        · rcases hM with ⟨m, hm⟩
          rcases hQ with ⟨q, hq⟩
          omega
        · exact hM
      exact ⟨hM, hQ⟩
  · rintro ⟨hM, hQ⟩
    exact (center_odd M Q hQ hs).2

/-- Theorem 3.3: the flow condition `w_s² ≥ 0` is `(u+1)² ≥ (D+1)² - x²`. -/
theorem flow_condition_iff (D x s : ℤ) :
    0 ≤ x ^ 2 - 4 * (D - s) * (D + 1 - (D - s)) ↔ (D + 1) ^ 2 - x ^ 2 ≤ (2 * s - D + 1) ^ 2 := by
  have hid : x ^ 2 - 4 * (D - s) * (D + 1 - (D - s)) =
      (2 * s - D + 1) ^ 2 - ((D + 1) ^ 2 - x ^ 2) := by ring
  rw [hid]
  omega

/-- §3.4: `x²U - (U-1)(E-U) = q(U)`. -/
theorem q_identity (x U E : ℤ) :
    x ^ 2 * U - (U - 1) * (E - U) = U ^ 2 - (E + 1 - x ^ 2) * U + E := by
  ring

/-- Corollary 3.4: `q(U₀) ≤ 0` for `0 ≤ x ≤ D`. -/
theorem q_flow_boundary_nonpos {D x : ℤ} (hD : 0 ≤ D) (hx : 0 ≤ x) (hxD : x ≤ D) :
    ((D + 1) ^ 2 - x ^ 2) ^ 2 - ((D + 3) ^ 2 + 1 - x ^ 2) * ((D + 1) ^ 2 - x ^ 2) +
      (D + 3) ^ 2 ≤ 0 := by
  have hxSq : x ^ 2 ≤ D ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hxD) (show 0 ≤ D + x by omega)
    nlinarith [hprod]
  have hbase : 0 ≤ 7 * D ^ 2 + 16 * D := by nlinarith
  have hbracket : 0 ≤ (D ^ 2 + 2 * D - x ^ 2) * (4 * D + 8) - x ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hxSq) (show 0 ≤ 4 * D + 9 by omega)
    nlinarith [hprod, hbase]
  have hid :
      ((D + 1) ^ 2 - x ^ 2) ^ 2 - ((D + 3) ^ 2 + 1 - x ^ 2) * ((D + 1) ^ 2 - x ^ 2) +
          (D + 3) ^ 2 = -((D ^ 2 + 2 * D - x ^ 2) * (4 * D + 8) - x ^ 2) := by
    ring
  rw [hid]
  omega

/-- Corollary 3.4 (coverage), `D = 0`. -/
theorem T_zero_zero : T 0 0 0 = 1 := by
  unfold T Tur
  rw [show (0 : ℤ) + 1 = 1 by norm_num]
  rw [show (0 : ℤ) - 1 = -1 by norm_num,
    show (1 : ℤ) - 1 = 0 by norm_num,
    show (1 : ℤ) + 1 = 2 by norm_num]
  rw [p_zero 0 0, p_of_neg 0 0 (by norm_num : (-1 : ℤ) < 0), p_one 0 0,
    p_of_gt 0 0 (by norm_num : (0 : ℤ) + 0 < 2)]
  norm_num

/-- Corollary 3.4 (coverage): every top-half cell is the top cell, the center, in the bulk
band, in the flow region, or a gap cell. -/
theorem coverage (M Q : ℕ) {s : ℤ} (h1 : (M : ℤ) + Q ≤ 2 * s) (h2 : s ≤ (M : ℤ) + Q) :
    s = (M : ℤ) + Q ∨ 2 * s = (M : ℤ) + Q ∨
      (1 ≤ 2 * s - ((M : ℤ) + Q) ∧
        ((M : ℤ) - Q) ^ 2 * (2 * s - ((M : ℤ) + Q) + 1) ^ 2 ≤
          ((2 * s - ((M : ℤ) + Q) + 1) ^ 2 - 1) *
            (((M : ℤ) + Q + 3) ^ 2 - (2 * s - ((M : ℤ) + Q) + 1) ^ 2)) ∨
      (s < (M : ℤ) + Q ∧
        ((M : ℤ) + Q + 1) ^ 2 - ((M : ℤ) - Q) ^ 2 ≤ (2 * s - ((M : ℤ) + Q) + 1) ^ 2) ∨
      Gap ((M : ℤ) + Q) ((M : ℤ) - Q) (2 * s - ((M : ℤ) + Q)) := by
  let D : ℤ := (M : ℤ) + Q
  let x : ℤ := (M : ℤ) - Q
  let u : ℤ := 2 * s - D
  by_cases htop : s = D
  · exact Or.inl htop
  · right
    by_cases hcenter : 2 * s = D
    · exact Or.inl hcenter
    · right
      have hu : 1 ≤ u := by dsimp [u, D]; omega
      by_cases hbulk : x ^ 2 * (u + 1) ^ 2 ≤
          ((u + 1) ^ 2 - 1) * ((D + 3) ^ 2 - (u + 1) ^ 2)
      · exact Or.inl ⟨hu, by simpa [u, D, x] using hbulk⟩
      · right
        by_cases hflow : (D + 1) ^ 2 - x ^ 2 ≤ (u + 1) ^ 2
        · exact Or.inl ⟨by omega, by simpa [u, D, x] using hflow⟩
        · right
          refine ⟨hu, ?_, ?_⟩
          · exact lt_of_not_ge hbulk
          · exact lt_of_not_ge hflow

/-- §3.4: for `Q ≥ 1`, Lemma 3.6 gives `30(u+1)² < 7(D+3)`. -/
theorem gap_strip_Q_pos {D x u Q : ℤ} (hg : Gap D x u) (hQ : 1 ≤ Q) (hx : 0 ≤ x)
    (hD : D = x + 2 * Q) : 30 * (u + 1) ^ 2 < 7 * (D + 3) := by
  have hstrip := gap_strip hg (by omega) hx hD
  have hcoef : 0 ≤ 6 * (2 * Q + 3) - 30 := by omega
  have hU : 0 ≤ (u + 1) ^ 2 := sq_nonneg _
  have hmul := mul_nonneg hcoef hU
  nlinarith [hstrip, hmul]

/-- §3.4: the first gap cell with `Q` odd and `u ≥ 2` is `(D,Q,u) = (84,1,2)`. -/
theorem first_odd_gap_cell :
    Gap 84 82 2 ∧
      ∀ D Q u : ℤ, 1 ≤ Q → Odd Q → 0 ≤ D - 2 * Q → 2 ≤ u → Even (D - u) →
        Gap D (D - 2 * Q) u → 84 ≤ D := by
  constructor
  · norm_num [Gap]
  · intro D Q u hQ hQodd hx hU hEven hg
    by_contra hD84
    have hDle : D ≤ 83 := by omega
    have hstrip : 30 * (u + 1) ^ 2 < 7 * (D + 3) :=
      gap_strip_Q_pos hg hQ hx (by omega)
    have huLe : u ≤ 3 := by
      by_contra h
      have h25 : 25 ≤ (u + 1) ^ 2 := by nlinarith
      nlinarith [hstrip, hDle, h25]
    have hDlo : 2 ≤ D := by omega
    have hxupper : D - 2 * Q ≤ D - 2 := by omega
    have hxsq : (D - 2 * Q) ^ 2 ≤ (D - 2) ^ 2 := by
      have hprod := mul_nonneg (by omega : 0 ≤ D - 2 - (D - 2 * Q))
        (by omega : 0 ≤ D - 2 + (D - 2 * Q))
      nlinarith [hprod]
    have hDprod : (D - 2) * (D - 83) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    rcases (show u = 2 ∨ u = 3 by omega) with hu | hu
    · have hbulk := hg.2.1
      rw [hu] at hbulk
      nlinarith [hbulk, hxsq, hDprod]
    · have hbulk := hg.2.1
      rw [hu] at hbulk
      nlinarith [hbulk, hxsq, hDprod]

end Kraw
