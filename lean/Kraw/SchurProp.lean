import Kraw.SchurJT
import Kraw.Main

/-!
# Proposition 1.3: the Schur-character interpretation (symmetric-function part)
-/

open MvPolynomial

namespace Kraw

private theorem prod_one_add_zSign (M Q : ℕ) :
    (∏ i : Fin (M + Q),
      (1 + Polynomial.C (zSign M Q i) * Polynomial.X : Polynomial ℤ)) = gen M Q := by
  rw [Fin.prod_univ_add]
  simp [zSign, gen, sub_eq_add_neg]

private theorem reverse_X_add_C_int (a : ℤ) :
    (Polynomial.X + Polynomial.C a : Polynomial ℤ).reverse =
      1 + Polynomial.C a * Polynomial.X := by
  rw [Polynomial.reverse_add_C]
  simp [Polynomial.reverse]

private theorem reverse_prod_linear_int {ι : Type*} (s : Finset ι) (z : ι → ℤ) :
    (∏ i ∈ s, (Polynomial.X + Polynomial.C (z i) : Polynomial ℤ)).reverse =
      ∏ i ∈ s, (1 + Polynomial.C (z i) * Polynomial.X : Polynomial ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.reverse]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      rw [Polynomial.reverse_mul_of_domain, reverse_X_add_C_int, ih]

private theorem eval_esymm_eq_powerset (D r : ℕ) (z : Fin D → ℤ) :
    eval z (esymm (Fin D) ℤ r) =
      ∑ t ∈ Finset.univ.powersetCard r, ∏ i ∈ t, z i := by
  simp [MvPolynomial.esymm]

private theorem eval_map_esymm_eq_powerset {K : Type*} [Field K]
    (D r : ℕ) (x : Fin D → K) :
    eval x (map (Int.castRingHom K) (esymm (Fin D) ℤ r)) =
      ∑ t ∈ Finset.univ.powersetCard r, ∏ i ∈ t, x i := by
  simp [MvPolynomial.esymm]

private theorem prod_inv_sdiff {K : Type*} [Field K] (D : ℕ) (x : Fin D → K)
    (hx : ∀ i, x i ≠ 0) (t : Finset (Fin D)) (ht : t ⊆ Finset.univ) :
    (∏ i ∈ t, (x i)⁻¹) = (∏ i, x i)⁻¹ * ∏ i ∈ Finset.univ \ t, x i := by
  rw [Finset.prod_inv_distrib]
  have htprod : (∏ i ∈ t, x i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact hx i
  have hcprod : (∏ i ∈ Finset.univ \ t, x i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact hx i
  rw [← Finset.prod_sdiff ht]
  field_simp [htprod, hcprod]

private theorem eval_map_esymm_inv_complement {K : Type*} [Field K]
    (D k : ℕ) (hk : k ≤ D) (x : Fin D → K) (hx : ∀ i, x i ≠ 0) :
    eval (fun i => (x i)⁻¹) (map (Int.castRingHom K) (esymm (Fin D) ℤ k)) =
      (∏ i, x i)⁻¹ *
        eval x (map (Int.castRingHom K) (esymm (Fin D) ℤ (D - k))) := by
  rw [eval_map_esymm_eq_powerset, eval_map_esymm_eq_powerset]
  calc
    (∑ t ∈ Finset.univ.powersetCard k, ∏ i ∈ t, (x i)⁻¹) =
        ∑ t ∈ Finset.univ.powersetCard k,
          (∏ i, x i)⁻¹ * ∏ i ∈ Finset.univ \ t, x i := by
      apply Finset.sum_congr rfl
      intro t ht
      exact prod_inv_sdiff D x hx t (Finset.mem_powersetCard.mp ht).1
    _ = (∏ i, x i)⁻¹ *
        ∑ t ∈ Finset.univ.powersetCard (D - k), ∏ i ∈ t, x i := by
      rw [← Finset.mul_sum]
      congr 1
      apply Finset.sum_bij'
        (fun t _ => (Finset.univ : Finset (Fin D)) \ t)
        (fun t _ => (Finset.univ : Finset (Fin D)) \ t)
      · intro t ht
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.sdiff_subset, ?_⟩
        rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp ht).1]
        simp only [Finset.card_univ, Fintype.card_fin, (Finset.mem_powersetCard.mp ht).2]
      · intro t ht
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.sdiff_subset, ?_⟩
        rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp ht).1]
        simp only [Finset.card_univ, Fintype.card_fin, (Finset.mem_powersetCard.mp ht).2]
        omega
      · intro t ht
        simp [(Finset.mem_powersetCard.mp ht).1]
      · intro t ht
        simp [(Finset.mem_powersetCard.mp ht).1]
      · intro t ht
        rfl

private theorem eval_map_schur_twoCol {K : Type*} [Field K] (D a b : ℕ)
    (hba : b ≤ a) (hb : 1 ≤ b) (x : Fin D → K) :
    eval x (map (Int.castRingHom K) (schur (twoCol a b hba) D)) =
      eval x (map (Int.castRingHom K) (esymm (Fin D) ℤ a)) *
        eval x (map (Int.castRingHom K) (esymm (Fin D) ℤ b)) -
      eval x (map (Int.castRingHom K) (esymm (Fin D) ℤ (a + 1))) *
        eval x (map (Int.castRingHom K) (esymm (Fin D) ℤ (b - 1))) := by
  rw [schur_twoCol D a b hba hb]
  simp

private theorem eval_map_schur_twoCol_zero {K : Type*} [Field K] (D a : ℕ)
    (x : Fin D → K) :
    eval x (map (Int.castRingHom K) (schur (twoCol a 0 (Nat.zero_le a)) D)) =
  eval x (map (Int.castRingHom K) (esymm (Fin D) ℤ a)) := by
  rw [schur_twoCol_zero]

/-- Proof of Proposition 1.3: the generating function of `p` is `∏ (1 + z_i w)`, so
`p_r = e_r(z)`. -/
theorem p_eq_esymm_zSign (M Q r : ℕ) :
    p M Q r = eval (zSign M Q) (esymm (Fin (M + Q)) ℤ r) := by
  let D := M + Q
  let z := zSign M Q
  let P : Polynomial ℤ := ∏ i : Fin D, (Polynomial.X + Polynomial.C (z i))
  have hPdeg : P.natDegree = D := by
    dsimp [P]
    rw [Polynomial.natDegree_prod_of_monic]
    · simp_rw [Polynomial.natDegree_X_add_C]
      simp [D]
    · intro i hi
      exact Polynomial.monic_X_add_C _
  have hgen : gen M Q = ∏ i : Fin D, (1 + Polynomial.C (z i) * Polynomial.X) := by
    simpa [D, z] using (prod_one_add_zSign M Q).symm
  have hrev : P.reverse = ∏ i : Fin D, (1 + Polynomial.C (z i) * Polynomial.X) := by
    simpa [P, D, z] using reverse_prod_linear_int (Finset.univ : Finset (Fin D)) z
  by_cases hr : r ≤ D
  · have hcoeff : (P.reverse).coeff r =
        ∑ t ∈ Finset.univ.powersetCard r, ∏ i ∈ t, z i := by
      calc
        (P.reverse).coeff r = P.coeff (D - r) := by
          rw [Polynomial.coeff_reverse, hPdeg, Polynomial.revAt_le hr]
        _ = ∑ t ∈ Finset.univ.powersetCard r, ∏ i ∈ t, z i := by
          have hvieta := Finset.prod_X_add_C_coeff (Finset.univ : Finset (Fin D)) z
            (k := D - r) (by simp)
          simpa [P, Nat.card_fin, Nat.sub_sub_self hr] using hvieta
    have hp : p M Q (r : ℤ) = (gen M Q).coeff r := by simp [p]
    rw [hp, hgen, ← hrev]
    exact hcoeff.trans (eval_esymm_eq_powerset D r z).symm
  · have hcoeff : (P.reverse).coeff r = 0 := by
      have hr' : D < r := by omega
      rw [Polynomial.coeff_reverse, hPdeg, Polynomial.revAt_eq_self_of_lt hr']
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hesymm : eval z (esymm (Fin D) ℤ r) = 0 := by
      rw [eval_esymm_eq_powerset]
      apply Finset.sum_eq_zero
      intro t ht
      have hcard : t.card = r := (Finset.mem_powersetCard.mp ht).2
      have hsub : t ⊆ (Finset.univ : Finset (Fin D)) := (Finset.mem_powersetCard.mp ht).1
      have : t.card ≤ D := by simpa using Finset.card_le_card hsub
      omega
    have hp : p M Q (r : ℤ) = (gen M Q).coeff r := by simp [p]
    rw [hp, hgen, ← hrev, hcoeff, hesymm]

/-- Proposition 1.3: `Tur(s) = s_{(2^s)}(z)` for `0 ≤ s ≤ D`. -/
theorem tur_eq_schur (M Q : ℕ) {s : ℕ} (hs : s ≤ M + Q) :
    Tur M Q s = eval (zSign M Q) (schur (rect s) (M + Q)) := by
  by_cases hs0 : s = 0
  · subst s
    rw [show rect 0 = twoCol 0 0 le_rfl by rfl]
    rw [schur_twoCol_zero]
    have hp0 : p M Q (0 : ℤ) = 1 := by
      simpa [MvPolynomial.esymm] using p_eq_esymm_zSign M Q 0
    have hpneg : p M Q (-1 : ℤ) = 0 := by simp [p]
    simp [Tur, hp0, hpneg]
  · have hspos : 1 ≤ s := by omega
    have hpPrev : p M Q ((s : ℤ) - 1) =
        eval (zSign M Q) (esymm (Fin (M + Q)) ℤ (s - 1)) := by
      simpa [Nat.cast_sub hspos] using p_eq_esymm_zSign M Q (s - 1)
    have hpNext : p M Q ((s : ℤ) + 1) =
        eval (zSign M Q) (esymm (Fin (M + Q)) ℤ (s + 1)) := by
      simpa using p_eq_esymm_zSign M Q (s + 1)
    rw [show rect s = twoCol s s le_rfl by rfl,
      schur_twoCol (M + Q) s s le_rfl hspos]
    simp only [eval_sub, eval_mul]
    unfold Tur
    simp_rw [hpPrev, hpNext, p_eq_esymm_zSign M Q s]
    ring

/-- Rectangle-complement identity (proof of Proposition 1.3): for `λ` inside the `2 × D`
rectangle with columns `a ≥ b`, the complement `λᶜ` has columns `D - b ≥ D - a` and
`s_λ(x⁻¹) = (x_1 ⋯ x_D)^{-2} s_{λᶜ}(x)`. -/
theorem schur_complement {K : Type*} [Field K] (D a b : ℕ) (hba : b ≤ a) (haD : a ≤ D)
    (x : Fin D → K) (hx : ∀ i, x i ≠ 0) :
    eval (fun i => (x i)⁻¹) (map (Int.castRingHom K) (schur (twoCol a b hba) D)) =
      ((∏ i, x i) ^ 2)⁻¹ *
        eval x (map (Int.castRingHom K) (schur (twoCol (D - b) (D - a) (by omega)) D)) := by
  let E : ℕ → K := fun k => eval x (map (Int.castRingHom K) (esymm (Fin D) ℤ k))
  let Ei : ℕ → K := fun k =>
    eval (fun i => (x i)⁻¹) (map (Int.castRingHom K) (esymm (Fin D) ℤ k))
  let P : K := ∏ i, x i
  change eval (fun i => (x i)⁻¹)
      (map (Int.castRingHom K) (schur (twoCol a b hba) D)) =
    (P ^ 2)⁻¹ * eval x
      (map (Int.castRingHom K) (schur (twoCol (D - b) (D - a) (by omega)) D))
  have hP : P ≠ 0 := by
    dsimp [P]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact hx i
  have hInv : ∀ k ≤ D, Ei k = P⁻¹ * E (D - k) := by
    intro k hk
    simpa [Ei, E, P] using eval_map_esymm_inv_complement D k hk x hx
  have hEzero : E 0 = 1 := by
    dsimp [E]
    rw [eval_map_esymm_eq_powerset]
    simp
  have hEtop : E D = P := by
    dsimp [E, P]
    rw [eval_map_esymm_eq_powerset]
    have hset : (Finset.univ : Finset (Fin D)).powersetCard D =
        {(Finset.univ : Finset (Fin D))} := by
      simpa using (Finset.powersetCard_self (Finset.univ : Finset (Fin D)))
    rw [hset]
    simp
  have hsetAbove : (Finset.univ : Finset (Fin D)).powersetCard (D + 1) = ∅ := by
    apply Finset.powersetCard_eq_empty.mpr
    simp
  have hEabove : E (D + 1) = 0 := by
    dsimp [E]
    rw [eval_map_esymm_eq_powerset, hsetAbove]
    simp
  have hEiAbove : Ei (D + 1) = 0 := by
    dsimp [Ei]
    rw [eval_map_esymm_eq_powerset, hsetAbove]
    simp
  by_cases hb0 : b = 0
  · subst b
    have hLeft :
        eval (fun i => (x i)⁻¹)
          (map (Int.castRingHom K) (schur (twoCol a 0 (Nat.zero_le a)) D)) = Ei a := by
      simpa [Ei] using eval_map_schur_twoCol_zero D a (fun i => (x i)⁻¹)
    by_cases haEq : a = D
    · subst a
      have hRight :
          eval x (map (Int.castRingHom K) (schur (twoCol D 0 (Nat.zero_le D)) D)) = E D := by
        simpa [E] using eval_map_schur_twoCol_zero D D x
      rw [show twoCol (D - 0) (D - D) (by omega) = twoCol D 0 (Nat.zero_le D) by simp]
      rw [hLeft, hRight, hInv D haD]
      simp only [Nat.sub_self]
      rw [hEzero, hEtop]
      field_simp [hP]
    · have haLt : a < D := by omega
      have hRight :
          eval x (map (Int.castRingHom K) (schur (twoCol D (D - a) (by omega)) D)) =
            E D * E (D - a) - E (D + 1) * E (D - a - 1) := by
        simpa [E, Nat.sub_zero] using
          eval_map_schur_twoCol D D (D - a) (by omega) (by omega) x
      rw [show twoCol (D - 0) (D - a) (by omega) = twoCol D (D - a) (by omega) by
        simp]
      rw [hLeft, hRight, hInv a haD, hEtop, hEabove]
      field_simp [hP]; ring
  · have hbpos : 1 ≤ b := by omega
    have hLeft :
        eval (fun i => (x i)⁻¹)
          (map (Int.castRingHom K) (schur (twoCol a b hba) D)) =
            Ei a * Ei b - Ei (a + 1) * Ei (b - 1) := by
      simpa [Ei] using eval_map_schur_twoCol D a b hba hbpos (fun i => (x i)⁻¹)
    by_cases haEq : a = D
    · subst a
      have hRight :
          eval x (map (Int.castRingHom K) (schur (twoCol (D - b) 0 (Nat.zero_le (D - b))) D)) =
            E (D - b) := by
        simpa [E] using eval_map_schur_twoCol_zero D (D - b) x
      rw [show twoCol (D - b) (D - D) (by omega) =
          twoCol (D - b) 0 (Nat.zero_le (D - b)) by simp]
      rw [hLeft, hRight, hInv D haD, hInv b (by omega), hEiAbove]
      simp only [Nat.sub_self]
      rw [hEzero]
      field_simp [hP]
      simp
    · have haLt : a < D := by omega
      have hRight :
          eval x (map (Int.castRingHom K) (schur (twoCol (D - b) (D - a) (by omega)) D)) =
            E (D - b) * E (D - a) - E (D - b + 1) * E (D - a - 1) := by
        simpa [E] using
          eval_map_schur_twoCol D (D - b) (D - a) (by omega) (by omega) x
      have haIdx : D - (a + 1) = D - a - 1 := by omega
      have hbIdx : D - (b - 1) = D - b + 1 := by omega
      rw [hLeft, hRight, hInv a haD, hInv b (by omega),
        hInv (a + 1) (by omega), hInv (b - 1) (by omega), haIdx, hbIdx]
      field_simp [hP]

/-- Proposition 1.3: `s_{(2^s)}(z) = s_{(2^{D-s})}(z)`, independently of the Main Theorem. -/
theorem schur_rect_symm (M Q : ℕ) {s : ℕ} (hs : s ≤ M + Q) :
    eval (zSign M Q) (schur (rect s) (M + Q)) =
      eval (zSign M Q) (schur (rect (M + Q - s)) (M + Q)) := by
  let D := M + Q
  let x : Fin D → ℚ := fun i => (zSign M Q i : ℚ)
  have hx : ∀ i, x i ≠ 0 := by
    intro i
    dsimp [x, zSign]
    split_ifs <;> norm_num
  have hinv : ∀ i, (x i)⁻¹ = x i := by
    intro i
    dsimp [x, zSign]
    split_ifs <;> norm_num
  have hprodSq : (∏ i, x i) ^ 2 = 1 := by
    rw [← Finset.prod_pow]
    simp [x, zSign]
  have hCastEval (f : MvPolynomial (Fin D) ℤ) :
      ((eval (zSign M Q) f : ℤ) : ℚ) =
        eval x (map (Int.castRingHom ℚ) f) := by
    simpa [x, Function.comp_def, MvPolynomial.eval_map] using
      MvPolynomial.eval₂_comp (Int.castRingHom ℚ) (zSign M Q) f
  have hRect :
      eval x (map (Int.castRingHom ℚ) (schur (rect s) D)) =
        eval x (map (Int.castRingHom ℚ) (schur (rect (D - s)) D)) := by
    have h := schur_complement (K := ℚ) D s s le_rfl hs x hx
    simpa [rect, hprodSq, hinv] using h
  apply Int.cast_injective (α := ℚ)
  calc
    ((eval (zSign M Q) (schur (rect s) D) : ℤ) : ℚ) =
        eval x (map (Int.castRingHom ℚ) (schur (rect s) D)) := hCastEval _
    _ = eval x (map (Int.castRingHom ℚ) (schur (rect (D - s)) D)) := hRect
    _ = ((eval (zSign M Q) (schur (rect (D - s)) D) : ℤ) : ℚ) := (hCastEval _).symm

end Kraw
