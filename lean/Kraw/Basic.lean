import Kraw.Defs

/-!
# Basic properties of the coefficients

Paper §2.1: support, initial values, the step-1 recurrence (2.1), reflection
`p_{D-j} = (-1)^Q p_j`, the `M ↔ Q` symmetry of `T`, and Lemma 2.1
(no two consecutive zeros).
-/

namespace Kraw

open Polynomial

variable (M Q : ℕ)

theorem p_of_neg {s : ℤ} (hs : s < 0) : p M Q s = 0 := by
  simp [p, hs]

private theorem natDegree_one_add_X_le : (1 + X : ℤ[X]).natDegree ≤ 1 := by
  have h : (1 + X : ℤ[X]) = X + C 1 := by rw [← C_1]; ring
  rw [h, Polynomial.natDegree_X_add_C]

private theorem natDegree_one_sub_X_le : (1 - X : ℤ[X]).natDegree ≤ 1 := by
  have h : (1 - X : ℤ[X]) = -(X - C 1) := by rw [← C_1]; ring
  rw [h, Polynomial.natDegree_neg]
  exact le_of_eq (Polynomial.natDegree_X_sub_C 1)

theorem gen_natDegree_le : (gen M Q).natDegree ≤ M + Q := by
  unfold gen
  calc
    ((1 + X : ℤ[X]) ^ M * (1 - X) ^ Q).natDegree ≤
        ((1 + X : ℤ[X]) ^ M).natDegree + ((1 - X : ℤ[X]) ^ Q).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ M + Q := by
      exact Nat.add_le_add
        (by simpa using Polynomial.natDegree_pow_le_of_le M natDegree_one_add_X_le)
        (by simpa using Polynomial.natDegree_pow_le_of_le Q natDegree_one_sub_X_le)

theorem p_of_gt {s : ℤ} (hs : (M : ℤ) + Q < s) : p M Q s = 0 := by
  have hs0 : 0 ≤ s := by omega
  have hsNat : M + Q < s.toNat := by
    exact_mod_cast (show (M : ℤ) + Q < (s.toNat : ℤ) by omega)
  have hdeg : (gen M Q).natDegree < s.toNat :=
    lt_of_le_of_lt (gen_natDegree_le M Q) hsNat
  simp [p, hs0, Polynomial.coeff_eq_zero_of_natDegree_lt hdeg]

theorem p_zero : p M Q 0 = 1 := by
  simp [p, gen, Polynomial.coeff_zero_eq_eval_zero]

private theorem p_nat_eq (n : ℕ) : p M Q (n : ℤ) = (gen M Q).coeff n := by
  simp [p]

private theorem derivative_one_add_pow (n : ℕ) :
    (1 + X : ℤ[X]) * derivative ((1 + X) ^ n) = C (n : ℤ) * (1 + X) ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Polynomial.derivative_pow]
    simp only [Nat.succ_sub_one, Polynomial.derivative_add, Polynomial.derivative_one,
      Polynomial.derivative_X, add_zero, one_mul]
    rw [pow_succ]
    ring

private theorem derivative_one_sub_pow (n : ℕ) :
    (1 - X : ℤ[X]) * derivative ((1 - X) ^ n) = -C (n : ℤ) * (1 - X) ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Polynomial.derivative_pow]
    simp only [Nat.succ_sub_one, Polynomial.derivative_sub, Polynomial.derivative_one,
      Polynomial.derivative_X, sub_zero, one_mul, neg_mul]
    rw [pow_succ]
    ring

private theorem gen_log_derivative :
    (1 - X ^ 2) * derivative (gen M Q) =
      (C ((M : ℤ) - Q) - C ((M : ℤ) + Q) * X) * gen M Q := by
  unfold gen
  rw [Polynomial.derivative_mul]
  calc
    (1 - X ^ 2) *
        (derivative ((1 + X : ℤ[X]) ^ M) * (1 - X) ^ Q +
          (1 + X) ^ M * derivative ((1 - X) ^ Q)) =
        (1 - X) * ((1 + X) * derivative ((1 + X : ℤ[X]) ^ M)) * (1 - X) ^ Q +
          (1 + X) ^ M * (1 + X) * ((1 - X) * derivative ((1 - X) ^ Q)) := by ring
    _ = (1 - X) * (C (M : ℤ) * (1 + X) ^ M) * (1 - X) ^ Q +
          (1 + X) ^ M * (1 + X) * (-C (Q : ℤ) * (1 - X) ^ Q) := by
          rw [derivative_one_add_pow, derivative_one_sub_pow]
    _ = (C ((M : ℤ) - Q) - C ((M : ℤ) + Q) * X) *
          ((1 + X : ℤ[X]) ^ M * (1 - X) ^ Q) := by
          simp only [map_sub, map_add]
          ring

private theorem gen_coeff_rec_zero :
    (gen M Q).coeff 1 = ((M : ℤ) - Q) * (gen M Q).coeff 0 := by
  have hc := congrArg (fun f : ℤ[X] => f.coeff 0) (gen_log_derivative (M := M) (Q := Q))
  rw [sub_mul, one_mul, sub_mul] at hc
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul', Polynomial.coeff_derivative,
    Polynomial.coeff_C_mul] at hc
  norm_num at hc ⊢
  exact hc

private theorem gen_coeff_rec (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℤ) * (gen M Q).coeff (n + 1) =
      ((M : ℤ) - Q) * (gen M Q).coeff n +
        (((n : ℕ) : ℤ) - 1 - ((M : ℤ) + Q)) * (gen M Q).coeff (n - 1) := by
  have hc := congrArg (fun f : ℤ[X] => f.coeff n) (gen_log_derivative (M := M) (Q := Q))
  rw [sub_mul, one_mul, sub_mul] at hc
  rw [mul_assoc] at hc
  have hX : (X * gen M Q).coeff n = if 1 ≤ n then (gen M Q).coeff (n - 1) else 0 := by
    simpa [pow_one] using (Polynomial.coeff_X_pow_mul' (gen M Q) 1 n)
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul', Polynomial.coeff_derivative,
    Polynomial.coeff_C_mul] at hc
  rw [hX] at hc
  by_cases hn2 : 2 ≤ n
  · have hnm : n - 2 + 1 = n - 1 := by omega
    simp only [if_pos hn2, if_pos (by omega : 1 ≤ n), hnm] at hc
    have hmul : ((n - 2 : ℕ) : ℤ) + 1 = ((n - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 1 ≤ n)]
      omega
    rw [hmul] at hc
    have hcastSub : ((n - 1 : ℕ) : ℤ) = (n : ℕ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [hcastSub] at hc
    push_cast at hc ⊢
    linear_combination hc
  · have hn1 : n = 1 := by omega
    subst n
    norm_num [Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul', Polynomial.coeff_derivative,
      Polynomial.coeff_C_mul] at hc ⊢
    linear_combination hc

/- The recurrence is extracted from the coefficient identity above. -/
theorem p_rec (s : ℤ) :
    (s + 1) * p M Q (s + 1) =
      ((M : ℤ) - Q) * p M Q s + (s - 1 - ((M : ℤ) + Q)) * p M Q (s - 1) := by
  cases s with
  | negSucc n => simp [p] <;> omega
  | ofNat n =>
    cases n with
    | zero =>
      have h := gen_coeff_rec_zero (M := M) (Q := Q)
      norm_num at h ⊢
      have hp1 : p M Q 1 = (gen M Q).coeff 1 := by
        change p M Q (Int.ofNat 1) = (gen M Q).coeff 1
        exact p_nat_eq M Q 1
      have hp0 : p M Q 0 = (gen M Q).coeff 0 := by
        change p M Q (Int.ofNat 0) = (gen M Q).coeff 0
        exact p_nat_eq M Q 0
      rw [p_of_neg (M := M) (Q := Q) (by norm_num : (-1 : ℤ) < 0),
        hp1, hp0]
      norm_num
      linear_combination h
    | succ n =>
      have h := gen_coeff_rec (M := M) (Q := Q) (n + 1) (by omega)
      have hsuc : Int.ofNat (n + 1) = (n : ℤ) + 1 := by simp
      have hp2 : p M Q (Int.ofNat (n + 1) + 1) = (gen M Q).coeff (n + 2) := by
        rw [hsuc]
        have hidx : (n : ℤ) + 1 + 1 = ((n + 2 : ℕ) : ℤ) := by omega
        rw [hidx]
        exact p_nat_eq M Q (n + 2)
      have hp1 : p M Q (Int.ofNat (n + 1)) = (gen M Q).coeff (n + 1) := by
        rw [hsuc]
        convert p_nat_eq M Q (n + 1) using 1 <;> simp [Int.natCast_succ]
      have hp0 : p M Q (Int.ofNat (n + 1) - 1) = (gen M Q).coeff n := by
        rw [hsuc]
        have hidx : (n : ℤ) + 1 - 1 = (n : ℤ) := by ring
        rw [hidx]
        exact p_nat_eq M Q n
      rw [hsuc] at hp2 hp1 hp0 ⊢
      rw [hp2, hp1, hp0]
      push_cast at h ⊢
      linear_combination h

theorem p_one : p M Q 1 = (M : ℤ) - Q := by
  have h := p_rec (M := M) (Q := Q) 0
  rw [show (0 : ℤ) + 1 = 1 by norm_num,
    show (0 : ℤ) - 1 = -1 by norm_num] at h
  rw [p_zero M Q,
    p_of_neg (M := M) (Q := Q) (by norm_num : (-1 : ℤ) < 0)] at h
  norm_num at h ⊢
  exact h

/-- Reflection `p_{D-j} = (-1)^Q p_j` (substitute `w ↦ 1/w`). -/
private theorem reflect_one_add_X : Polynomial.reflect 1 (1 + X : ℤ[X]) = 1 + X := by
  simp [Polynomial.reflect_one, Polynomial.reflect_monomial, Polynomial.revAt]
  ring

private theorem reflect_one_sub_X : Polynomial.reflect 1 (1 - X : ℤ[X]) = -(1 - X) := by
  simp [Polynomial.reflect_sub, Polynomial.reflect_one, Polynomial.reflect_monomial,
    Polynomial.revAt]

private theorem reflect_one_add_pow (n : ℕ) :
    Polynomial.reflect n ((1 + X : ℤ[X]) ^ n) = (1 + X) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : ((1 + X : ℤ[X]) ^ n).natDegree ≤ n := by
      simpa using Polynomial.natDegree_pow_le_of_le n natDegree_one_add_X_le
    rw [pow_succ, Polynomial.reflect_mul (Ff := hpow) (Gg := natDegree_one_add_X_le)]
    rw [ih, reflect_one_add_X]

private theorem reflect_one_sub_pow (n : ℕ) :
    Polynomial.reflect n ((1 - X : ℤ[X]) ^ n) = C ((-1 : ℤ) ^ n) * (1 - X) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : ((1 - X : ℤ[X]) ^ n).natDegree ≤ n := by
      simpa using Polynomial.natDegree_pow_le_of_le n natDegree_one_sub_X_le
    calc
      Polynomial.reflect (n + 1) ((1 - X : ℤ[X]) ^ (n + 1)) =
          Polynomial.reflect n ((1 - X : ℤ[X]) ^ n) *
            Polynomial.reflect 1 (1 - X : ℤ[X]) := by
          rw [pow_succ, Polynomial.reflect_mul (Ff := hpow) (Gg := natDegree_one_sub_X_le)]
      _ = C ((-1 : ℤ) ^ n) * (1 - X) ^ n * (-(1 - X)) := by
          rw [ih, reflect_one_sub_X]
      _ = C ((-1 : ℤ) ^ (n + 1)) * (1 - X) ^ (n + 1) := by
          rw [pow_succ, Polynomial.C_mul]
          simp [Polynomial.C_neg]
          ring

private theorem gen_reflect :
    Polynomial.reflect (M + Q) (gen M Q) = C ((-1 : ℤ) ^ Q) * gen M Q := by
  unfold gen
  have hM : ((1 + X : ℤ[X]) ^ M).natDegree ≤ M := by
    simpa using Polynomial.natDegree_pow_le_of_le M natDegree_one_add_X_le
  have hQ : ((1 - X : ℤ[X]) ^ Q).natDegree ≤ Q := by
    simpa using Polynomial.natDegree_pow_le_of_le Q natDegree_one_sub_X_le
  rw [Polynomial.reflect_mul (Ff := hM) (Gg := hQ), reflect_one_add_pow, reflect_one_sub_pow]
  ring

private theorem p_refl_nat (j : ℕ) (hj : j ≤ M + Q) :
    p M Q ((M + Q - j : ℕ) : ℤ) = (-1 : ℤ) ^ Q * p M Q (j : ℤ) := by
  have hc := congrArg (fun f : ℤ[X] => f.coeff j) (gen_reflect (M := M) (Q := Q))
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le hj, Polynomial.coeff_C_mul] at hc
  calc
    p M Q ((M + Q - j : ℕ) : ℤ) = (gen M Q).coeff (M + Q - j) :=
      p_nat_eq M Q (M + Q - j)
    _ = (-1 : ℤ) ^ Q * (gen M Q).coeff j := hc
    _ = (-1 : ℤ) ^ Q * p M Q (j : ℤ) := by rw [← p_nat_eq M Q j]

theorem p_refl (j : ℤ) : p M Q ((M : ℤ) + Q - j) = (-1) ^ Q * p M Q j := by
  by_cases hj0 : 0 ≤ j
  · by_cases hjD : j ≤ (M : ℤ) + Q
    · let n := j.toNat
      have hn : (n : ℤ) = j := Int.toNat_of_nonneg hj0
      have hnD : n ≤ M + Q := by
        have h : (n : ℤ) ≤ (M + Q : ℕ) := by simpa [hn] using hjD
        exact_mod_cast h
      have h := p_refl_nat (M := M) (Q := Q) n hnD
      have hidx : ((M + Q - n : ℕ) : ℤ) = (M : ℤ) + Q - j := by
        rw [Nat.cast_sub hnD]
        simp [hn]
      simpa [hn, hidx] using h
    · have hjgt : (M : ℤ) + Q < j := by omega
      have hjneg : (M : ℤ) + Q - j < 0 := by omega
      rw [p_of_neg (M := M) (Q := Q) hjneg, p_of_gt (M := M) (Q := Q) hjgt]
      ring
  · have hjneg : j < 0 := by omega
    have hgt : (M : ℤ) + Q < (M : ℤ) + Q - j := by omega
    rw [p_of_gt (M := M) (Q := Q) hgt, p_of_neg (M := M) (Q := Q) hjneg]
    simp

theorem p_top : p M Q ((M : ℤ) + Q) = (-1) ^ Q := by
  simpa [p_zero] using p_refl (M := M) (Q := Q) 0

private theorem neg_X_pow (n : ℕ) : (-X : ℤ[X]) ^ n = C ((-1 : ℤ) ^ n) * X ^ n := by
  calc
    (-X : ℤ[X]) ^ n = (C (-1) * X) ^ n := by congr 1 <;> simp
    _ = C (-1) ^ n * X ^ n := mul_pow _ _ _
    _ = C ((-1 : ℤ) ^ n) * X ^ n := by simp

private theorem coeff_comp_neg (f : ℤ[X]) (n : ℕ) :
    (f.comp (-X)).coeff n = (-1 : ℤ) ^ n * f.coeff n := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]; ring
  | monomial k a =>
    have hpoly : C a * (-X : ℤ[X]) ^ k = C (a * (-1 : ℤ) ^ k) * X ^ k := by
      rw [neg_X_pow]
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

private theorem gen_swap_poly : gen Q M = (gen M Q).comp (-X) := by
  unfold gen
  simp [Polynomial.comp, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  ring

private theorem p_swap_nat (n : ℕ) :
    p Q M (n : ℤ) = (-1 : ℤ) ^ n * p M Q (n : ℤ) := by
  have h := congrArg (fun f : ℤ[X] => f.coeff n) (gen_swap_poly (M := M) (Q := Q))
  rw [coeff_comp_neg] at h
  calc
    p Q M (n : ℤ) = (gen Q M).coeff n := p_nat_eq Q M n
    _ = (-1 : ℤ) ^ n * (gen M Q).coeff n := h
    _ = (-1 : ℤ) ^ n * p M Q (n : ℤ) := by rw [← p_nat_eq M Q n]

private theorem neg_one_pow_even (n : ℕ) : (-1 : ℤ) ^ (2 * n) = 1 := by
  rw [pow_mul]
  norm_num

private theorem neg_one_pow_pair (n : ℕ) :
    (-1 : ℤ) ^ n * (-1 : ℤ) ^ (n + 2) = 1 := by
  rw [← pow_add, show n + (n + 2) = 2 * (n + 1) by omega, neg_one_pow_even]

private theorem tur_swap_nat (n : ℕ) :
    Tur Q M (n : ℤ) = Tur M Q (n : ℤ) := by
  cases n with
  | zero => simp [Tur, p_zero, p_of_neg]
  | succ n =>
    have hprev : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
    have hnext : ((n + 1 : ℕ) : ℤ) + 1 = ((n + 2 : ℕ) : ℤ) := by omega
    unfold Tur
    rw [hprev, hnext]
    rw [p_swap_nat M Q (n + 1), p_swap_nat M Q n, p_swap_nat M Q (n + 2)]
    have hsquare : ((-1 : ℤ) ^ (n + 1)) ^ 2 = 1 := by
      rw [pow_two, ← pow_add, show (n + 1) + (n + 1) = 2 * (n + 1) by omega,
        neg_one_pow_even]
    calc
      ((-1 : ℤ) ^ (n + 1) * p M Q ((n + 1 : ℕ) : ℤ)) ^ 2 -
          (-1 : ℤ) ^ n * p M Q (n : ℤ) *
            ((-1 : ℤ) ^ (n + 2) * p M Q ((n + 2 : ℕ) : ℤ)) =
          ((-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (n + 1)) *
              p M Q ((n + 1 : ℕ) : ℤ) ^ 2 -
            ((-1 : ℤ) ^ n * (-1 : ℤ) ^ (n + 2)) *
              p M Q (n : ℤ) * p M Q ((n + 2 : ℕ) : ℤ) := by ring
      _ = p M Q ((n + 1 : ℕ) : ℤ) ^ 2 -
            p M Q (n : ℤ) * p M Q ((n + 2 : ℕ) : ℤ) := by
          have hsquare' : (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (n + 1) = 1 := by
            calc
              (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (n + 1) =
                  ((-1 : ℤ) ^ (n + 1)) ^ 2 := by rw [pow_two]
              _ = 1 := hsquare
          rw [hsquare', neg_one_pow_pair]
          ring

/-- `T` is invariant under `M ↔ Q` (substitute `w ↦ -w`; every product in `T`
has even index sum). -/
theorem T_swap (s : ℤ) : T Q M s = T M Q s := by
  cases s with
  | ofNat n =>
    have h0 := tur_swap_nat (M := M) (Q := Q) n
    have h1 := tur_swap_nat (M := M) (Q := Q) (n + 1)
    have h1' : Tur Q M ((n : ℤ) + 1) = Tur M Q ((n : ℤ) + 1) := by
      simpa [Int.natCast_succ] using h1
    unfold T
    change Tur Q M (n : ℤ) - Tur Q M ((n : ℤ) + 1) =
      Tur M Q (n : ℤ) - Tur M Q ((n : ℤ) + 1)
    rw [h0, h1']
  | negSucc n =>
    cases n with
    | zero => simp [T, Tur, p_zero, p_of_neg]
    | succ n => simp [T, Tur, p_zero, p_of_neg, p] <;> split_ifs <;> omega

/-- Lemma 2.1: two consecutive coefficients never both vanish. -/
private theorem no_consec_zero_nat : ∀ n : ℕ, n ≤ M + Q →
    (p M Q (n : ℤ) = 0 ∧ p M Q ((n : ℤ) + 1) = 0) → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hpair
    by_cases hn0 : n = 0
    · subst n
      change p M Q (0 : ℤ) = 0 ∧ p M Q ((0 : ℤ) + 1) = 0 at hpair
      have hfirst := hpair.1
      rw [p_zero M Q] at hfirst
      norm_num at hfirst
    · have hnpos : 1 ≤ n := by omega
      have hrec := p_rec (M := M) (Q := Q) (n : ℤ)
      rw [hpair.1, hpair.2] at hrec
      have hmul : ((n : ℤ) - 1 - ((M : ℤ) + Q)) * p M Q ((n : ℤ) - 1) = 0 := by
        nlinarith [hrec]
      have hfactor : (n : ℤ) - 1 - ((M : ℤ) + Q) ≠ 0 := by omega
      have hprev : p M Q ((n : ℤ) - 1) = 0 := by
        rcases mul_eq_zero.mp hmul with h | h
        · exact (hfactor h).elim
        · exact h
      have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        rw [Nat.cast_sub hnpos, Nat.cast_one]
      have hindex : ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by
        exact_mod_cast (Nat.sub_add_cancel hnpos)
      have hprevPair : p M Q ((n - 1 : ℕ) : ℤ) = 0 ∧
          p M Q (((n - 1 : ℕ) : ℤ) + 1) = 0 := by
        constructor
        · rw [hcast]
          exact hprev
        · rw [hindex]
          exact hpair.1
      exact ih (n - 1) (by omega) (by omega) hprevPair

theorem no_consec_zero {j : ℤ} (h0 : 0 ≤ j) (hj : j ≤ (M : ℤ) + Q) :
    ¬ (p M Q j = 0 ∧ p M Q (j + 1) = 0) := by
  intro hpair
  let n := j.toNat
  have hn : (n : ℤ) = j := Int.toNat_of_nonneg h0
  have hnD : n ≤ M + Q := by
    have h : (n : ℤ) ≤ (M + Q : ℕ) := by simpa [hn] using hj
    exact_mod_cast h
  have hpairNat : p M Q (n : ℤ) = 0 ∧ p M Q ((n : ℤ) + 1) = 0 := by
    constructor
    · simpa [hn] using hpair.1
    · simpa [hn] using hpair.2
  exact no_consec_zero_nat (M := M) (Q := Q) n hnD hpairNat

theorem Tur_refl (s : ℤ) : Tur M Q ((M : ℤ) + Q - s) = Tur M Q s := by
  have hprev : (M : ℤ) + Q - s - 1 = (M : ℤ) + Q - (s + 1) := by ring
  have hnext : (M : ℤ) + Q - s + 1 = (M : ℤ) + Q - (s - 1) := by ring
  unfold Tur
  rw [hprev, hnext, p_refl M Q s, p_refl M Q (s + 1), p_refl M Q (s - 1)]
  have hsign : (-1 : ℤ) ^ (Q * 2) = 1 := by
    rw [show Q * 2 = 2 * Q by omega, neg_one_pow_even]
  have hsignPair : (-1 : ℤ) ^ Q * (-1 : ℤ) ^ Q = 1 := by
    calc
      (-1 : ℤ) ^ Q * (-1 : ℤ) ^ Q = (-1 : ℤ) ^ (Q + Q) := by rw [← pow_add]
      _ = (-1 : ℤ) ^ (Q * 2) := by congr 1 <;> omega
      _ = 1 := hsign
  calc
    ((-1 : ℤ) ^ Q * p M Q s) ^ 2 -
        (-1 : ℤ) ^ Q * p M Q (s + 1) * ((-1 : ℤ) ^ Q * p M Q (s - 1)) =
        ((-1 : ℤ) ^ Q * (-1 : ℤ) ^ Q) * p M Q s ^ 2 -
          ((-1 : ℤ) ^ Q * (-1 : ℤ) ^ Q) * p M Q (s + 1) * p M Q (s - 1) := by ring
    _ = p M Q s ^ 2 - p M Q (s - 1) * p M Q (s + 1) := by rw [hsignPair]; ring

theorem Tur_top : Tur M Q ((M : ℤ) + Q) = 1 := by
  have htop := p_top M Q
  have hzero := p_of_gt (M := M) (Q := Q)
    (show (M : ℤ) + Q < (M : ℤ) + Q + 1 by omega)
  unfold Tur
  rw [htop, hzero]
  have hsign : ((-1 : ℤ) ^ Q) ^ 2 = 1 := by
    calc
      ((-1 : ℤ) ^ Q) ^ 2 = (-1 : ℤ) ^ (2 * Q) := by
        rw [pow_two, ← pow_add]
        congr 1
        omega
      _ = 1 := neg_one_pow_even Q
  rw [hsign]
  ring

end Kraw
