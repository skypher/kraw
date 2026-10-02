import Kraw.Main

/-!
# Binary Krawtchouk polynomials (paper §1.1, §1.3)
-/

open Polynomial

namespace Kraw

/-- The binary Krawtchouk polynomial in the generating-function normalization,
`K_k(x;N) = Σ_{j=0}^{k} (-1)^j C(x,j) C(N-x,k-j)`, a polynomial in `x`, where
`C(y,j) = y(y-1)⋯(y-j+1)/j!`. -/
noncomputable def krawtchouk (N k : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (k + 1),
    C ((-1) ^ j / ((j.factorial : ℚ) * ((k - j).factorial : ℚ))) *
      descPochhammer ℚ j * (descPochhammer ℚ (k - j)).comp (C (N : ℚ) - X)

private noncomputable def krawtchoukGenerating (N x : ℕ) : ℚ[X] :=
  (1 + X) ^ (N - x) * (1 - X) ^ x

private theorem coeff_one_sub_X_pow (n m : ℕ) :
    ((1 - X : ℚ[X]) ^ n).coeff m = (-1 : ℚ) ^ m * (n.choose m : ℚ) := by
  have hfactor : (1 - X : ℚ[X]) = -(X + C (-1)) := by
    simp only [sub_eq_add_neg, C_neg, C_1, neg_add, neg_neg]
    ac_rfl
  rw [hfactor, neg_pow,
    show ((-1 : ℚ[X]) ^ n) = C ((-1 : ℚ) ^ n) by simp,
    coeff_C_mul, coeff_X_add_C_pow]
  by_cases hmn : m ≤ n
  · have hexp : n + (n - m) = m + 2 * (n - m) := by omega
    have hpow : (-1 : ℚ) ^ n * (-1) ^ (n - m) = (-1 : ℚ) ^ m := by
      calc
        (-1 : ℚ) ^ n * (-1) ^ (n - m) = (-1 : ℚ) ^ (n + (n - m)) := by rw [← pow_add]
        _ = (-1 : ℚ) ^ (m + 2 * (n - m)) := by rw [hexp]
        _ = (-1 : ℚ) ^ m := by simp [pow_add, pow_mul]
    rw [← mul_assoc, hpow]
  · have hzero : n.choose m = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hmn)
    simp [hzero]

private theorem eval_descPochhammer_eq_factorial_mul_choose (n j : ℕ) :
    (descPochhammer ℚ j).eval (n : ℚ) = (j.factorial : ℚ) * (n.choose j : ℚ) := by
  rw [descPochhammer_eval_eq_descFactorial]
  exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n j

private theorem krawtchouk_eval_eq_coeff (N x k : ℕ) (hx : x ≤ N) :
    (krawtchouk N k).eval (x : ℚ) = (krawtchoukGenerating N x).coeff k := by
  have harg : (C (N : ℚ) - X : ℚ[X]).eval (x : ℚ) = ((N - x : ℕ) : ℚ) := by
    simp [Nat.cast_sub hx]
  have hsum :
      (krawtchouk N k).eval (x : ℚ) =
        ∑ j ∈ Finset.range (k + 1),
          (-1 : ℚ) ^ j * (x.choose j : ℚ) * ((N - x).choose (k - j) : ℚ) := by
    unfold krawtchouk
    rw [eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [eval_mul, eval_mul, eval_C, eval_comp, harg,
      eval_descPochhammer_eq_factorial_mul_choose,
      eval_descPochhammer_eq_factorial_mul_choose]
    field_simp [Nat.factorial_ne_zero]
  rw [hsum, krawtchoukGenerating,
    mul_comm ((1 + X : ℚ[X]) ^ (N - x)) ((1 - X) ^ x), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [coeff_one_sub_X_pow, coeff_one_add_X_pow]

private theorem krawtchoukGenerating_natDegree_le (N x : ℕ) (hx : x ≤ N) :
    (krawtchoukGenerating N x).natDegree ≤ N := by
  have hplus : (1 + X : ℚ[X]).natDegree = 1 := by
    simpa [C_1, add_comm] using (natDegree_X_add_C (1 : ℚ))
  have hminus : (1 - X : ℚ[X]).natDegree = 1 := by
    have hlin : (1 - X : ℚ[X]) = -(X - C (1 : ℚ)) := by
      simp only [C_1, sub_eq_add_neg, neg_add, neg_neg]
      ac_rfl
    calc
      (1 - X : ℚ[X]).natDegree = (-(X - C (1 : ℚ))).natDegree := congrArg natDegree hlin
      _ = (X - C (1 : ℚ)).natDegree := natDegree_neg _
      _ = 1 := natDegree_X_sub_C (1 : ℚ)
  unfold krawtchoukGenerating
  calc
    ((1 + X : ℚ[X]) ^ (N - x) * ((1 : ℚ[X]) - X) ^ x).natDegree ≤
        ((1 + X : ℚ[X]) ^ (N - x)).natDegree + (((1 : ℚ[X]) - X) ^ x).natDegree :=
      natDegree_mul_le
    _ = N := by simp [hplus, hminus, Nat.sub_add_cancel hx]

private noncomputable def krawtchoukTerm (N k j : ℕ) : ℚ[X] :=
  C ((-1) ^ j / ((j.factorial : ℚ) * ((k - j).factorial : ℚ))) *
    descPochhammer ℚ j * (descPochhammer ℚ (k - j)).comp (C (N : ℚ) - X)

private theorem natDegree_descPochhammer (n : ℕ) :
    (descPochhammer ℚ n).natDegree = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm : (descPochhammer ℚ n).Monic := monic_descPochhammer ℚ n
    have hcast : (n : ℚ[X]) = C (n : ℚ) := by simp
    have hmul :
        (descPochhammer ℚ n).leadingCoeff * (X - (n : ℚ[X])).leadingCoeff ≠ 0 := by
      rw [hm.leadingCoeff, hcast, leadingCoeff_X_sub_C]
      norm_num
    rw [descPochhammer_succ_right, natDegree_mul' hmul, ih, hcast, natDegree_X_sub_C]

private theorem krawtchoukAffine_natDegree (N : ℕ) :
    (C (N : ℚ) - X : ℚ[X]).natDegree = 1 := by
  have hlin : (C (N : ℚ) - X : ℚ[X]) = -(X - C (N : ℚ)) := by ring
  rw [hlin, natDegree_neg, natDegree_X_sub_C]

private theorem krawtchoukAffine_leadingCoeff (N : ℕ) :
    (C (N : ℚ) - X : ℚ[X]).leadingCoeff = -1 := by
  have hlin : (C (N : ℚ) - X : ℚ[X]) = -(X - C (N : ℚ)) := by ring
  calc
    (C (N : ℚ) - X : ℚ[X]).leadingCoeff = (-(X - C (N : ℚ))).leadingCoeff :=
      congrArg leadingCoeff hlin
    _ = -1 := by
      change (-(X - C (N : ℚ))).leadingCoeff = -1
      rw [leadingCoeff_neg, leadingCoeff_X_sub_C]

private theorem krawtchoukTerm_natDegree (N k j : ℕ) (hj : j ≤ k) :
    (krawtchoukTerm N k j).natDegree = k := by
  let c : ℚ := (-1) ^ j / ((j.factorial : ℚ) * ((k - j).factorial : ℚ))
  have hc : c ≠ 0 := by
    dsimp [c]
    apply div_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · exact mul_ne_zero
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - j)))
  have hmon : (descPochhammer ℚ j).Monic := monic_descPochhammer ℚ j
  have hcompLc :
      ((descPochhammer ℚ (k - j)).comp (C (N : ℚ) - X)).leadingCoeff =
        (-1 : ℚ) ^ (k - j) := by
    rw [leadingCoeff_comp (by rw [krawtchoukAffine_natDegree]; norm_num),
      (monic_descPochhammer ℚ (k - j)).leadingCoeff, krawtchoukAffine_leadingCoeff,
      natDegree_descPochhammer]
    simp
  have hleftLc : (C c * descPochhammer ℚ j).leadingCoeff = c := hmon.leadingCoeff_C_mul c
  have hmul :
      (C c * descPochhammer ℚ j).leadingCoeff *
        ((descPochhammer ℚ (k - j)).comp (C (N : ℚ) - X)).leadingCoeff ≠ 0 := by
    rw [hleftLc, hcompLc]
    exact mul_ne_zero hc (pow_ne_zero _ (by norm_num))
  change ((C c * descPochhammer ℚ j) *
      (descPochhammer ℚ (k - j)).comp (C (N : ℚ) - X)).natDegree = k
  rw [natDegree_mul' hmul, natDegree_C_mul hc, natDegree_descPochhammer,
    natDegree_comp, natDegree_descPochhammer, krawtchoukAffine_natDegree]
  simp [Nat.add_sub_of_le hj]

private theorem krawtchoukTerm_leadingCoeff (N k j : ℕ) (hj : j ≤ k) :
    (krawtchoukTerm N k j).leadingCoeff =
      (-1 : ℚ) ^ k / (k.factorial : ℚ) * (k.choose j : ℚ) := by
  let c : ℚ := (-1) ^ j / ((j.factorial : ℚ) * ((k - j).factorial : ℚ))
  have hc : c ≠ 0 := by
    dsimp [c]
    apply div_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · exact mul_ne_zero
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - j)))
  have hmon : (descPochhammer ℚ j).Monic := monic_descPochhammer ℚ j
  have hcompLc :
      ((descPochhammer ℚ (k - j)).comp (C (N : ℚ) - X)).leadingCoeff =
        (-1 : ℚ) ^ (k - j) := by
    rw [leadingCoeff_comp (by rw [krawtchoukAffine_natDegree]; norm_num),
      (monic_descPochhammer ℚ (k - j)).leadingCoeff, krawtchoukAffine_leadingCoeff,
      natDegree_descPochhammer]
    simp
  have hleftLc : (C c * descPochhammer ℚ j).leadingCoeff = c := hmon.leadingCoeff_C_mul c
  have hmul :
      (C c * descPochhammer ℚ j).leadingCoeff *
        ((descPochhammer ℚ (k - j)).comp (C (N : ℚ) - X)).leadingCoeff ≠ 0 := by
    rw [hleftLc, hcompLc]
    exact mul_ne_zero hc (pow_ne_zero _ (by norm_num))
  have htermLc :
      (krawtchoukTerm N k j).leadingCoeff = c * (-1 : ℚ) ^ (k - j) := by
    change ((C c * descPochhammer ℚ j) *
      (descPochhammer ℚ (k - j)).comp (C (N : ℚ) - X)).leadingCoeff = _
    rw [leadingCoeff_mul' hmul, hleftLc, hcompLc]
  have hsign : (-1 : ℚ) ^ j * (-1) ^ (k - j) = (-1 : ℚ) ^ k := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  have hchoose :
      (k.choose j : ℚ) * (j.factorial : ℚ) * ((k - j).factorial : ℚ) =
        (k.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  rw [htermLc]
  calc
    c * (-1 : ℚ) ^ (k - j) = (-1 : ℚ) ^ k /
        ((j.factorial : ℚ) * ((k - j).factorial : ℚ)) := by
          dsimp [c]
          rw [← hsign]
          ring
    _ = (-1 : ℚ) ^ k / (k.factorial : ℚ) * (k.choose j : ℚ) := by
          have hden : (j.factorial : ℚ) * ((k - j).factorial : ℚ) ≠ 0 :=
            mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero j)
              (by exact_mod_cast Nat.factorial_ne_zero (k - j))
          have hfact : (k.factorial : ℚ) ≠ 0 := by
            exact_mod_cast Nat.factorial_ne_zero k
          have hinv :
              ((j.factorial : ℚ) * ((k - j).factorial : ℚ))⁻¹ =
                (k.choose j : ℚ) / (k.factorial : ℚ) := by
            field_simp [hden, hfact]
            nlinarith [hchoose]
          calc
            (-1 : ℚ) ^ k / ((j.factorial : ℚ) * ((k - j).factorial : ℚ)) =
                (-1 : ℚ) ^ k *
                  ((j.factorial : ℚ) * ((k - j).factorial : ℚ))⁻¹ := by rw [div_eq_mul_inv]
            _ = (-1 : ℚ) ^ k * ((k.choose j : ℚ) / (k.factorial : ℚ)) := by rw [hinv]
            _ = (-1 : ℚ) ^ k / (k.factorial : ℚ) * (k.choose j : ℚ) := by ring

private theorem krawtchouk_coeff_k (N k : ℕ) :
    (krawtchouk N k).coeff k = (-2 : ℚ) ^ k / (k.factorial : ℚ) := by
  unfold krawtchouk
  rw [finsetSum_coeff]
  calc
    (∑ j ∈ Finset.range (k + 1), (krawtchoukTerm N k j).coeff k) =
        ∑ j ∈ Finset.range (k + 1),
          (-1 : ℚ) ^ k / (k.factorial : ℚ) * (k.choose j : ℚ) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjle : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
            calc
              (krawtchoukTerm N k j).coeff k = (krawtchoukTerm N k j).leadingCoeff := by
                calc
                  (krawtchoukTerm N k j).coeff k =
                      (krawtchoukTerm N k j).coeff (krawtchoukTerm N k j).natDegree :=
                        congrArg (krawtchoukTerm N k j).coeff
                          (krawtchoukTerm_natDegree N k j hjle).symm
                  _ = (krawtchoukTerm N k j).leadingCoeff := coeff_natDegree
              _ = (-1 : ℚ) ^ k / (k.factorial : ℚ) * (k.choose j : ℚ) :=
                krawtchoukTerm_leadingCoeff N k j hjle
    _ = ((-1 : ℚ) ^ k / (k.factorial : ℚ)) * 2 ^ k := by
          rw [← Finset.mul_sum, ← Nat.cast_sum, Nat.sum_range_choose]
          simp
    _ = (-2 : ℚ) ^ k / (k.factorial : ℚ) := by
          have hpow : (-2 : ℚ) ^ k = (-1 : ℚ) ^ k * 2 ^ k := by
            rw [show (-2 : ℚ) = (-1) * 2 by norm_num, mul_pow]
          rw [hpow]
          ring

private theorem krawtchouk_natDegree_aux (N k : ℕ) : (krawtchouk N k).natDegree = k := by
  have hle : (krawtchouk N k).natDegree ≤ k := by
    apply natDegree_sum_le_of_forall_le (s := Finset.range (k + 1))
    intro j hj
    exact le_of_eq (krawtchoukTerm_natDegree N k j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  apply natDegree_eq_of_le_of_coeff_ne_zero hle
  rw [krawtchouk_coeff_k]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero k)

private abbrev KrawtchoukBivar := Polynomial (Polynomial ℚ)

private noncomputable def krawtchoukInnerConstant (p : ℚ[X]) : KrawtchoukBivar := Polynomial.C p

private noncomputable def krawtchoukBivarConstant (r : ℚ) : KrawtchoukBivar :=
  krawtchoukInnerConstant (Polynomial.C r)

private noncomputable def krawtchoukGeneratingPair (N x : ℕ) : KrawtchoukBivar :=
  (Polynomial.map Polynomial.C (krawtchoukGenerating N x)) *
    Polynomial.C (krawtchoukGenerating N x)

private theorem krawtchouk_bivar_generating_identity (N : ℕ) :
    ∑ x ∈ Finset.range (N + 1),
        krawtchoukBivarConstant (N.choose x : ℚ) * krawtchoukGeneratingPair N x =
      krawtchoukBivarConstant (2 ^ N : ℚ) *
        (1 + (X : KrawtchoukBivar) * Polynomial.C (X : ℚ[X])) ^ N := by
  let W : KrawtchoukBivar := X
  let V : KrawtchoukBivar := Polynomial.C (X : ℚ[X])
  let A : KrawtchoukBivar := (1 + W) * (1 + V)
  let B : KrawtchoukBivar := (1 - W) * (1 - V)
  have hmap (x : ℕ) :
      Polynomial.map Polynomial.C (krawtchoukGenerating N x) =
        (1 + W) ^ (N - x) * (1 - W) ^ x := by
    simp [krawtchoukGenerating, W, map_mul, map_pow]
  have hconstant (x : ℕ) :
      (Polynomial.C (krawtchoukGenerating N x) : KrawtchoukBivar) =
        (1 + V) ^ (N - x) * (1 - V) ^ x := by
    simp [krawtchoukGenerating, V, map_mul, map_pow]
  have hterm (x : ℕ) : krawtchoukGeneratingPair N x = A ^ (N - x) * B ^ x := by
    unfold krawtchoukGeneratingPair
    rw [hmap, hconstant]
    calc
      (1 + W) ^ (N - x) * (1 - W) ^ x * ((1 + V) ^ (N - x) * (1 - V) ^ x) =
          ((1 + W) ^ (N - x) * (1 + V) ^ (N - x)) *
            ((1 - W) ^ x * (1 - V) ^ x) := by ac_rfl
      _ = ((1 + W) * (1 + V)) ^ (N - x) * ((1 - W) * (1 - V)) ^ x := by
            rw [← mul_pow, ← mul_pow]
      _ = A ^ (N - x) * B ^ x := rfl
  have hBA : B + A = krawtchoukBivarConstant (2 : ℚ) * (1 + W * V) := by
    change B + A = (2 : KrawtchoukBivar) * (1 + W * V)
    dsimp [A, B]
    ring
  calc
    _ = ∑ x ∈ Finset.range (N + 1),
        krawtchoukBivarConstant (N.choose x : ℚ) * (A ^ (N - x) * B ^ x) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hterm]
    _ = (B + A) ^ N := by
          symm
          calc
            (B + A) ^ N =
                ∑ x ∈ Finset.range (N + 1), B ^ x * A ^ (N - x) * (N.choose x : KrawtchoukBivar) :=
              add_pow B A N
            _ = ∑ x ∈ Finset.range (N + 1),
                krawtchoukBivarConstant (N.choose x : ℚ) * (A ^ (N - x) * B ^ x) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  simp [krawtchoukBivarConstant, krawtchoukInnerConstant]
                  ring
    _ = krawtchoukBivarConstant (2 ^ N : ℚ) *
          (1 + (X : KrawtchoukBivar) * Polynomial.C (X : ℚ[X])) ^ N := by
          rw [hBA, mul_pow]
          simp [W, V, krawtchoukBivarConstant, krawtchoukInnerConstant, C_pow]

private theorem krawtchouk_bivar_power_coeff (N m : ℕ) :
    ((1 + (X : KrawtchoukBivar) * Polynomial.C (X : ℚ[X])) ^ N).coeff m =
      if m ≤ N then
        Polynomial.C (N.choose m : ℚ) * (X : ℚ[X]) ^ m
      else 0 := by
  let W : KrawtchoukBivar := X
  let V : KrawtchoukBivar := Polynomial.C (X : ℚ[X])
  have hexp : (1 + W * V) ^ N =
      ∑ i ∈ Finset.range (N + 1),
        Polynomial.C (Polynomial.C (N.choose i : ℚ)) *
          Polynomial.C ((X : ℚ[X]) ^ i) * W ^ i := by
    rw [show 1 + W * V = W * V + 1 by ac_rfl, add_pow]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [mul_pow, one_pow]
    have hV : V ^ i = Polynomial.C ((X : ℚ[X]) ^ i) := by simp [V]
    have hcast : (N.choose i : KrawtchoukBivar) =
        Polynomial.C (Polynomial.C (N.choose i : ℚ)) := by
      simp [krawtchoukBivarConstant, krawtchoukInnerConstant]
    rw [hV, hcast]
    ac_rfl
  rw [hexp, finsetSum_coeff]
  simp_rw [← Polynomial.C_mul]
  simp only [coeff_C_mul_X_pow, W]
  by_cases hm : m ≤ N
  · have hmem : m ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
    rw [Finset.sum_eq_single m]
    · simp [hm]
    · intro i hi hne
      simp [Ne.symm hne]
    · intro hnot
      exact (hnot hmem).elim
  · have hlt : N < m := Nat.lt_of_not_ge hm
    rw [Finset.sum_eq_zero]
    · simp [hm]
    · intro i hi
      have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hne : m ≠ i := by omega
      simp [hne]

private theorem krawtchouk_bivar_kernel_coeff (N k l : ℕ) :
    ((krawtchoukBivarConstant (2 ^ N : ℚ) *
        (1 + (X : KrawtchoukBivar) * Polynomial.C (X : ℚ[X])) ^ N).coeff k).coeff l =
      if k = l then 2 ^ N * (N.choose k : ℚ) else 0 := by
  dsimp [krawtchoukBivarConstant, krawtchoukInnerConstant]
  rw [coeff_C_mul, krawtchouk_bivar_power_coeff]
  by_cases hk : k ≤ N
  · simp only [if_pos hk]
    by_cases hkl : k = l
    · subst l
      simp only [← C_pow, coeff_C_mul, coeff_C_mul_X_pow]
      simp
    · simp only [← C_pow, coeff_C_mul, coeff_C_mul_X_pow]
      simp [hkl, Ne.symm hkl]
  · have hkN : N < k := Nat.lt_of_not_ge hk
    simp [hk, Nat.choose_eq_zero_of_lt hkN, C_pow, coeff_C_mul]

private theorem krawtchoukGeneratingPair_coeff (N x k l : ℕ) (hx : x ≤ N) :
    ((krawtchoukBivarConstant (N.choose x : ℚ) *
        krawtchoukGeneratingPair N x).coeff k).coeff l =
      (N.choose x : ℚ) * (krawtchouk N k).eval (x : ℚ) *
        (krawtchouk N l).eval (x : ℚ) := by
  change ((Polynomial.C (Polynomial.C (N.choose x : ℚ)) *
      (Polynomial.map Polynomial.C (krawtchoukGenerating N x) *
        Polynomial.C (krawtchoukGenerating N x))).coeff k).coeff l = _
  rw [coeff_C_mul, coeff_mul_C, coeff_map, coeff_C_mul, coeff_C_mul]
  rw [← krawtchouk_eval_eq_coeff N x k hx, ← krawtchouk_eval_eq_coeff N x l hx]
  ring

/-- §1.1: the generating function `Σ_k K_k(x;N) w^k = (1+w)^{N-x}(1-w)^x` at integers
`0 ≤ x ≤ N`. -/
theorem krawtchouk_genfun (N x : ℕ) (hx : x ≤ N) :
    ∑ k ∈ Finset.range (N + 1), C ((krawtchouk N k).eval (x : ℚ)) * X ^ k =
      (1 + X) ^ (N - x) * (1 - X) ^ x := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range (N + 1)) :
      C ((krawtchouk N k).eval (x : ℚ)) * X ^ k =
        C ((krawtchoukGenerating N x).coeff k) * X ^ k := by
    rw [krawtchouk_eval_eq_coeff N x k hx]
  calc
    _ = ∑ k ∈ Finset.range (N + 1),
        C ((krawtchoukGenerating N x).coeff k) * X ^ k := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hterm k hk
    _ = krawtchoukGenerating N x := by
          symm
          apply as_sum_range_C_mul_X_pow'
          exact lt_of_le_of_lt (krawtchoukGenerating_natDegree_le N x hx) (Nat.lt_succ_self N)
    _ = (1 + X) ^ (N - x) * (1 - X) ^ x := rfl

theorem krawtchouk_eval_eq_zero (N x k : ℕ) (hx : x ≤ N) (hk : N < k) :
    (krawtchouk N k).eval (x : ℚ) = 0 := by
  rw [krawtchouk_eval_eq_coeff N x k hx]
  apply coeff_eq_zero_of_natDegree_lt
  exact (krawtchoukGenerating_natDegree_le N x hx).trans_lt hk

/-- §1.1: `p_s = K_s(Q; D)`. -/
theorem p_eq_krawtchouk (M Q s : ℕ) : (p M Q s : ℚ) = (krawtchouk (M + Q) s).eval (Q : ℚ) := by
  have hmap :
      (gen M Q).map (Int.castRingHom ℚ) = krawtchoukGenerating (M + Q) Q := by
    simp [gen, krawtchoukGenerating, map_mul, map_pow, Nat.add_sub_cancel_right]
  have hcoeff : ((gen M Q).coeff s : ℚ) =
      (krawtchoukGenerating (M + Q) Q).coeff s := by
    rw [← hmap, coeff_map]
    simp
  rw [krawtchouk_eval_eq_coeff (M + Q) Q s (Nat.le_add_left Q M), ← hcoeff]
  simp [p]

/-- `K_k(·;N)` has leading coefficient `(-2)^k / k!`, hence degree exactly `k`. -/
theorem krawtchouk_leadingCoeff (N k : ℕ) :
    (krawtchouk N k).leadingCoeff = (-2) ^ k / (k.factorial : ℚ) := by
  rw [leadingCoeff, krawtchouk_natDegree_aux, krawtchouk_coeff_k]

theorem krawtchouk_natDegree (N k : ℕ) : (krawtchouk N k).natDegree = k := by
  exact krawtchouk_natDegree_aux N k

/-- §1.3: orthogonality for the binomial weight,
`Σ_x C(N,x) K_k(x) K_l(x) = 2^N C(N,k) δ_{kl}`. -/
theorem krawtchouk_orthogonal (N k l : ℕ) :
    ∑ x ∈ Finset.range (N + 1),
        (N.choose x : ℚ) * (krawtchouk N k).eval (x : ℚ) * (krawtchouk N l).eval (x : ℚ) =
      if k = l then 2 ^ N * (N.choose k : ℚ) else 0 := by
  have hsum :
      ((∑ x ∈ Finset.range (N + 1),
          krawtchoukBivarConstant (N.choose x : ℚ) * krawtchoukGeneratingPair N x).coeff k).coeff l =
        ∑ x ∈ Finset.range (N + 1),
          (N.choose x : ℚ) * (krawtchouk N k).eval (x : ℚ) *
            (krawtchouk N l).eval (x : ℚ) := by
    rw [finsetSum_coeff, finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro x hx
    exact krawtchoukGeneratingPair_coeff N x k l
      (Nat.le_of_lt_succ (Finset.mem_range.mp hx))
  calc
    _ = ((∑ x ∈ Finset.range (N + 1),
        krawtchoukBivarConstant (N.choose x : ℚ) * krawtchoukGeneratingPair N x).coeff k).coeff l :=
          hsum.symm
    _ = ((krawtchoukBivarConstant (2 ^ N : ℚ) *
        (1 + (X : KrawtchoukBivar) * Polynomial.C (X : ℚ[X])) ^ N).coeff k).coeff l :=
          congrArg (fun p : KrawtchoukBivar => (p.coeff k).coeff l)
            (krawtchouk_bivar_generating_identity N)
    _ = if k = l then 2 ^ N * (N.choose k : ℚ) else 0 :=
          krawtchouk_bivar_kernel_coeff N k l

end Kraw
