import Kraw.Krawtchouk
import Kraw.SeqDefs

/-!
# The role of the normalization (paper §1.3)
-/

namespace Kraw

/-- §1.3: rescaling `q_s = c_s p_s` multiplies the Turán determinant at `s` by one positive
factor for every sequence `p` iff `c_s ≠ 0` and `c_s² = c_{s-1} c_{s+1}`. -/
theorem turan_rescale_iff (c₀ c₁ c₂ : ℝ) :
    (∃ μ > 0, ∀ a b d : ℝ, (c₁ * b) ^ 2 - (c₀ * a) * (c₂ * d) = μ * (b ^ 2 - a * d)) ↔
      (c₁ ≠ 0 ∧ c₁ ^ 2 = c₀ * c₂) := by
  constructor
  · rintro ⟨μ, hμ, hscale⟩
    have h₁ := hscale 0 1 0
    have h₂ := hscale 1 0 1
    constructor
    · intro hc
      rw [hc] at h₁
      norm_num at h₁
      linarith
    · nlinarith [h₁, h₂]
  · rintro ⟨hc, hflat⟩
    refine ⟨c₁ ^ 2, sq_pos_of_ne_zero hc, ?_⟩
    intro a b d
    calc
      (c₁ * b) ^ 2 - (c₀ * a) * (c₂ * d) = c₁ ^ 2 * b ^ 2 - (c₀ * c₂) * (a * d) := by ring
      _ = c₁ ^ 2 * (b ^ 2 - a * d) := by rw [← hflat]; ring

/-- §1.3: a nowhere-vanishing sequence has `c_s² = c_{s-1} c_{s+1}` for all `s` iff it is
geometric. -/
theorem log_flat_iff_geometric (c : ℤ → ℝ) (hc : ∀ s, c s ≠ 0) :
    (∀ s, c s ^ 2 = c (s - 1) * c (s + 1)) ↔ ∃ a r : ℝ, r ≠ 0 ∧ ∀ s : ℤ, c s = a * r ^ s := by
  constructor
  · intro hflat
    let r : ℝ := c 1 / c 0
    have hr : r ≠ 0 := by
      dsimp [r]
      exact div_ne_zero (hc 1) (hc 0)
    have hratioStep (s : ℤ) : c (s + 1) / c s = c s / c (s - 1) := by
      apply (div_eq_div_iff (hc s) (hc (s - 1))).2
      nlinarith [hflat s]
    have hratio : ∀ s : ℤ, c (s + 1) / c s = r := by
      intro s
      induction s using Int.induction_on with
      | zero => simp [r]
      | succ s ih =>
          have hs := hratioStep ((s : ℤ) + 1)
          calc
            c ((s : ℤ) + 1 + 1) / c ((s : ℤ) + 1) =
                c ((s : ℤ) + 1) / c (((s : ℤ) + 1) - 1) := hs
            _ = c ((s : ℤ) + 1) / c (s : ℤ) := by simp
            _ = r := ih
      | pred s ih =>
          have ht : -(s : ℤ) - 1 + 1 = -(s : ℤ) := by omega
          calc
            c (-(s : ℤ) - 1 + 1) / c (-(s : ℤ) - 1) =
                c (-(s : ℤ)) / c (-(s : ℤ) - 1) := by rw [ht]
            _ = c (-(s : ℤ) + 1) / c (-(s : ℤ)) := (hratioStep (-(s : ℤ))).symm
            _ = r := ih
    have hmul (s : ℤ) : c (s + 1) = c s * r := by
      calc
        c (s + 1) = (c (s + 1) / c s) * c s := by field_simp [hc s]
        _ = r * c s := by rw [hratio s]
        _ = c s * r := by ring
    have hseq : ∀ s : ℤ, c s = c 0 * r ^ s := by
      intro s
      induction s using Int.induction_on with
      | zero => simp
      | succ s ih =>
          calc
            c ((s : ℤ) + 1) = c (s : ℤ) * r := hmul (s : ℤ)
            _ = (c 0 * r ^ (s : ℤ)) * r := by rw [ih]
            _ = c 0 * r ^ ((s : ℤ) + 1) := by rw [zpow_add_one₀ hr (s : ℤ)]; ring
      | pred s ih =>
          let t : ℤ := -(s : ℤ)
          have hratio' : c t / c (t - 1) = r := by
            calc
              c t / c (t - 1) = c (t + 1) / c t := (hratioStep t).symm
              _ = r := hratio t
          have hmul' : c t = r * c (t - 1) :=
            (div_eq_iff (hc (t - 1))).mp hratio'
          have hprev : c (t - 1) = c t / r := by
            rw [hmul']
            field_simp [hr]
          calc
            c (t - 1) = c t / r := hprev
            _ = (c 0 * r ^ t) / r := by rw [ih]
            _ = c 0 * r ^ (t - 1) := by
              rw [zpow_sub_one₀ hr t]
              field_simp [hr]
    exact ⟨c 0, r, hr, hseq⟩
  · rintro ⟨a, r, hr, hgeom⟩ s
    rw [hgeom s, hgeom (s - 1), hgeom (s + 1), zpow_sub_one₀ hr s, zpow_add_one₀ hr s]
    field_simp [hr]

/-- The squared norm of `K_s(·;D)` for the binomial probability weight `C(D,x)/2^D`. -/
noncomputable def krawNormSq (D s : ℕ) : ℝ :=
  ∑ x ∈ Finset.range (D + 1),
    ((D.choose x : ℝ) / 2 ^ D) * (((krawtchouk D s).eval (x : ℚ) : ℚ) : ℝ) ^ 2

theorem krawNormSq_eq (D s : ℕ) : krawNormSq D s = D.choose s := by
  have horth := krawtchouk_orthogonal D s s
  simp at horth
  have horthR :
      ∑ x ∈ Finset.range (D + 1),
        (D.choose x : ℝ) *
          (((krawtchouk D s).eval (x : ℚ) : ℚ) : ℝ) *
          (((krawtchouk D s).eval (x : ℚ) : ℚ) : ℝ) =
        (2 : ℝ) ^ D * (D.choose s : ℝ) := by
    exact_mod_cast horth
  have hden : (2 : ℝ) ^ D ≠ 0 := by positivity
  unfold krawNormSq
  calc
    (∑ x ∈ Finset.range (D + 1),
        ((D.choose x : ℝ) / 2 ^ D) *
          (((krawtchouk D s).eval (x : ℚ) : ℚ) : ℝ) ^ 2) =
        ∑ x ∈ Finset.range (D + 1),
          (((D.choose x : ℝ) *
              (((krawtchouk D s).eval (x : ℚ) : ℚ) : ℝ) *
              (((krawtchouk D s).eval (x : ℚ) : ℚ) : ℝ)) / (2 : ℝ) ^ D) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (∑ x ∈ Finset.range (D + 1),
          (D.choose x : ℝ) *
            (((krawtchouk D s).eval (x : ℚ) : ℚ) : ℝ) *
            (((krawtchouk D s).eval (x : ℚ) : ℚ) : ℝ)) / (2 : ℝ) ^ D := by
      exact (Finset.sum_div _ _ _).symm
    _ = (2 : ℝ) ^ D * (D.choose s : ℝ) / (2 : ℝ) ^ D := by rw [horthR]
    _ = D.choose s := by field_simp [hden]

/-- The orthonormal normalization `K_s(Q;D)/‖K_s‖`, as a sequence in `s`. -/
noncomputable def pOrth (M Q : ℕ) (s : ℤ) : ℝ :=
  if 0 ≤ s ∧ s ≤ (M : ℤ) + Q then (p M Q s : ℝ) / Real.sqrt (krawNormSq (M + Q) s.toNat) else 0

/-- The endpoint normalization `K_s(Q;D)/K_s(0;D)`, as a sequence in `s`. -/
noncomputable def pEnd (M Q : ℕ) (s : ℤ) : ℝ :=
  if 0 ≤ s ∧ s ≤ (M : ℤ) + Q then
    (p M Q s : ℝ) / (((krawtchouk (M + Q) s.toNat).eval 0 : ℚ) : ℝ) else 0

/-- §1.3: the orthonormal normalization does not preserve Theorem 1.1. -/
theorem orthonormal_not_monotone :
    ∃ M Q : ℕ, ∃ s : ℤ, (M : ℤ) + Q ≤ 2 * s ∧ s ≤ (M : ℤ) + Q ∧ stepSeq (pOrth M Q) s < 0 := by
  refine ⟨2, 1, 2, by norm_num, by norm_num, ?_⟩
  have hN₁ : krawNormSq 3 1 = 3 := by rw [krawNormSq_eq]; norm_num
  have hN₂ : krawNormSq 3 2 = 3 := by rw [krawNormSq_eq]; norm_num
  have hN₃ : krawNormSq 3 3 = 1 := by rw [krawNormSq_eq]; norm_num
  have hp₀ : p 2 1 0 = 1 := p_zero 2 1
  have hp₁ : p 2 1 1 = 1 := by rw [p_one]; norm_num
  have hp₂ : p 2 1 2 = -1 := by
    have h := p_rec 2 1 1
    norm_num [hp₀, hp₁] at h ⊢
    linarith
  have hp₃ : p 2 1 3 = -1 := by
    have h := p_rec 2 1 2
    norm_num [hp₁, hp₂] at h ⊢
    linarith
  have hf₁ : pOrth 2 1 1 = 1 / Real.sqrt 3 := by
    norm_num [pOrth, hp₁, hN₁]
  have hto₂ : Int.toNat (2 : ℤ) = 2 := rfl
  have hto₃ : Int.toNat (3 : ℤ) = 3 := rfl
  have hf₂ : pOrth 2 1 2 = -1 / Real.sqrt 3 := by
    norm_num [pOrth, hp₂, hN₂, hto₂]
  have hf₃ : pOrth 2 1 3 = -1 := by
    norm_num [pOrth, hp₃, hN₃, hto₃]
  have hf₄ : pOrth 2 1 4 = 0 := by norm_num [pOrth]
  have hstep : stepSeq (pOrth 2 1) 2 = 1 / 3 + 1 / Real.sqrt 3 - 1 := by
    unfold stepSeq turSeq
    norm_num [hf₁, hf₂, hf₃, hf₄]
    have hsqrt : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
    rw [hsqrt]
  have hsqrtPos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrtLower : (3 : ℝ) / 2 < Real.sqrt 3 := by nlinarith [hsqrtPos, hsqrtSq]
  have hrecip : 1 / Real.sqrt 3 < (2 : ℝ) / 3 := by
    apply (div_lt_iff₀ hsqrtPos).2
    nlinarith [hsqrtLower]
  rw [hstep]
  nlinarith [hrecip]

/-- §1.3: the endpoint normalization does not preserve Theorem 1.1. -/
theorem endpoint_not_monotone :
    ∃ M Q : ℕ, ∃ s : ℤ, (M : ℤ) + Q ≤ 2 * s ∧ s ≤ (M : ℤ) + Q ∧ stepSeq (pEnd M Q) s < 0 := by
  refine ⟨2, 0, 1, by norm_num, by norm_num, ?_⟩
  have hp₀ : p 2 0 0 = 1 := p_zero 2 0
  have hp₁ : p 2 0 1 = 2 := by rw [p_one]; norm_num
  have hp₂ : p 2 0 2 = 1 := by
    have h := p_rec 2 0 1
    norm_num [hp₀, hp₁] at h ⊢
    linarith
  have hgf :
      ∑ k ∈ Finset.range 3,
        Polynomial.C (((krawtchouk 2 k).eval (0 : ℚ))) * Polynomial.X ^ k =
          (1 + Polynomial.X) ^ 2 := by
    simpa using krawtchouk_genfun 2 0 (by norm_num)
  have hk₀ : (krawtchouk 2 0).eval 0 = 1 := by
    have h := congrArg (fun f : Polynomial ℚ => f.coeff 0) hgf
    norm_num [Polynomial.coeff_sum, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at h
    simpa [Polynomial.coeff_one_add_X_pow] using h
  have hk₁ : (krawtchouk 2 1).eval 0 = 2 := by
    have h := congrArg (fun f : Polynomial ℚ => f.coeff 1) hgf
    norm_num [Polynomial.coeff_sum, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at h
    simpa [Polynomial.coeff_one_add_X_pow] using h
  have hk₂ : (krawtchouk 2 2).eval 0 = 1 := by
    have h := congrArg (fun f : Polynomial ℚ => f.coeff 2) hgf
    norm_num [Polynomial.coeff_sum, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at h
    simpa [Polynomial.coeff_one_add_X_pow] using h
  have hto₂ : Int.toNat (2 : ℤ) = 2 := rfl
  have hf₀ : pEnd 2 0 0 = 1 := by
    norm_num [pEnd, hp₀, hk₀]
  have hf₁ : pEnd 2 0 1 = 1 := by
    norm_num [pEnd, hp₁, hk₁]
  have hf₂ : pEnd 2 0 2 = 1 := by
    norm_num [pEnd, hp₂, hk₂, hto₂]
  have hf₃ : pEnd 2 0 3 = 0 := by norm_num [pEnd]
  simp [stepSeq, turSeq, hf₀, hf₁, hf₂, hf₃]

end Kraw
