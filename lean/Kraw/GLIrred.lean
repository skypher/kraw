import Kraw.GLCyclic

/-! Irreducibility of `W = ker E`, and of `Λ^0 ⊗ Λ^0`. -/

namespace Kraw

private theorem transferCoord_basis_real (D s : ℕ)
    (p : PairIdx D s s) (q : PairIdx D (s + 1) (s - 1)) :
    star (transferCoord D s (Pi.single p 1) q) = transferCoord D s (Pi.single p 1) q := by
  classical
  rcases q with ⟨qA, qB⟩
  change star ((coordinateTensorBasis D (s + 1) (s - 1)).equivFun
    (transferMap D s ((coordinateTensorBasis D s s).equivFun.symm (Pi.single p 1)))
      (qA, qB)) = _
  have hs : (coordinateTensorBasis D s s).equivFun.symm (Pi.single p 1) =
      coordinateTensorBasis D s s p := by
    apply (coordinateTensorBasis D s s).equivFun.injective
    ext r
    simp [Pi.single_apply]
  delta transferCoord pairCoord
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  conv_lhs => rw [hs]
  conv_rhs => rw [hs]
  rw [transferMap, Module.Basis.constr_basis]
  change star ((coordinateTensorBasis D (s + 1) (s - 1)).equivFun.toLinearMap
    (∑ i : Fin D, if hiA : i ∉ p.1.1 then
      if hiB : i ∈ p.2.1 then
        (wedgePositionSign p.1.1 i * wedgePositionSign p.2.1 i) •
          (coordinateWedgeBasis D (s + 1) (insertCoordinate p.1 i hiA) ⊗ₜ[ℂ]
            coordinateWedgeBasis D (s - 1) (eraseCoordinate p.2 i hiB))
      else 0 else 0) (qA, qB)) = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    coordinateTensorBasis, Module.Basis.tensorProduct_apply,
    Module.Basis.equivFun_self]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hA : i ∈ p.1.1
  · simp [hA, LinearEquiv.map_zero, LinearEquiv.map_smulₛₗ, starRingEnd_apply]
  · by_cases hB : i ∈ p.2.1
    · simp [hA, hB, LinearEquiv.map_zero, LinearEquiv.map_smulₛₗ, Finsupp.single_apply]
      rw [starRingEnd_apply]
      by_cases hqA : insertCoordinate p.1 i hA = qA
      · by_cases hqB : eraseCoordinate p.2 i hB = qB
        · simp [hqA, hqB, wedgePositionSign]
        · simp [hqA, hqB, wedgePositionSign]
      · simp [hqA, wedgePositionSign]
    · simp [hA, hB, LinearEquiv.map_zero, LinearEquiv.map_smulₛₗ, starRingEnd_apply]

private theorem transferCoord_conj (D s : ℕ) (x : PairIdx D s s → ℂ) :
    transferCoord D s (fun p => star (x p)) = fun q => star (transferCoord D s x q) := by
  classical
  let ι := PairIdx D s s
  have expansion (y : ι → ℂ) : y = ∑ p, y p • Pi.single p 1 := by
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using
      ((Pi.basisFun ℂ ι).sum_repr y).symm
  ext q
  have evalExpansion (y : ι → ℂ) :
      transferCoord D s y q =
        ∑ p : PairIdx D s s, y p * transferCoord D s (Pi.single p 1) q := by
    calc
      transferCoord D s y q =
          transferCoord D s (∑ p : PairIdx D s s, y p • Pi.single p 1) q :=
        congrArg (fun z => transferCoord D s z q) (expansion y)
      _ = ∑ p : PairIdx D s s, y p * transferCoord D s (Pi.single p 1) q := by
        simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    transferCoord D s (fun p => star (x p)) q =
        ∑ p : PairIdx D s s, star (x p) * transferCoord D s (Pi.single p 1) q :=
      evalExpansion _
    _ = star (∑ p : PairIdx D s s, x p * transferCoord D s (Pi.single p 1) q) := by
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [star_mul, transferCoord_basis_real, mul_comm]
    _ = star (transferCoord D s x q) := congrArg star (evalExpansion x).symm

private noncomputable def wedgeMinorMatrix (D s : ℕ) (g : GL (Fin D) ℂ)
    (A C : Set.powersetCard (Fin D) s) : Matrix (Fin s) (Fin s) ℂ :=
  fun i j => (g : Matrix (Fin D) (Fin D) ℂ)
    ((Set.powersetCard.ofFinEmbEquiv.symm C) j)
    ((Set.powersetCard.ofFinEmbEquiv.symm A) i)

private theorem exteriorCoeff_eq_det (D s : ℕ) (g : GL (Fin D) ℂ)
    (A C : Set.powersetCard (Fin D) s) :
      (coordinateWedgeBasis D s).repr
        (exteriorPowerRep D s g (coordinateWedgeBasis D s A)) C =
      (wedgeMinorMatrix D s g A C).det := by
  simp only [coordinateWedgeBasis, exteriorPowerRep, standardRep]
  change ((Pi.basisFun ℂ (Fin D)).exteriorPower s).repr
    (exteriorPower.map s (Matrix.toLin' (g : Matrix (Fin D) (Fin D) ℂ))
      ((Pi.basisFun ℂ (Fin D)).exteriorPower s A)) C = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti]
  apply congrArg Matrix.det
  ext i j
  simp [wedgeMinorMatrix, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Pi.basisFun_repr, Pi.basisFun_apply]

private noncomputable def glTranspose {D : ℕ} (g : GL (Fin D) ℂ) : GL (Fin D) ℂ where
  val := Matrix.transpose (g : Matrix (Fin D) (Fin D) ℂ)
  inv := Matrix.transpose g.inv
  val_inv := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
      congrArg Matrix.transpose g.inv_val
  inv_val := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
      congrArg Matrix.transpose g.val_inv

private theorem wedgeMinorMatrix_transpose (D s : ℕ) (g : GL (Fin D) ℂ)
    (A C : Set.powersetCard (Fin D) s) :
    wedgeMinorMatrix D s (glTranspose g) A C =
      Matrix.transpose (wedgeMinorMatrix D s g C A) := by
  ext i j
  simp [wedgeMinorMatrix, glTranspose, Matrix.transpose_apply]

private theorem exteriorCoeff_transpose (D s : ℕ) (g : GL (Fin D) ℂ)
    (A C : Set.powersetCard (Fin D) s) :
    (coordinateWedgeBasis D s).repr
        (exteriorPowerRep D s (glTranspose g) (coordinateWedgeBasis D s A)) C =
      (coordinateWedgeBasis D s).repr
        (exteriorPowerRep D s g (coordinateWedgeBasis D s C)) A := by
  rw [exteriorCoeff_eq_det, exteriorCoeff_eq_det, wedgeMinorMatrix_transpose]
  simpa only [Matrix.det_transpose]

private theorem prod_embedding_eq_subset (D s : ℕ)
    (A : Set.powersetCard (Fin D) s) (f : Fin D → ℂ) :
    ∏ j : Fin s, f ((Set.powersetCard.ofFinEmbEquiv.symm A) j) =
      ∏ i ∈ A.1, f i := by
  classical
  let e := Set.powersetCard.ofFinEmbEquiv.symm A
  have he : Finset.univ.map e.toEmbedding = A.1 := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    simpa [e, Set.mem_range, Set.powersetCard.mem_coe_iff] using
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A i)
  simpa [he] using
    (Finset.prod_map (Finset.univ : Finset (Fin s)) e.toEmbedding f).symm

private theorem exteriorCoeff_diagGL (D s : ℕ) (t : Fin D → ℂˣ)
    (A C : Set.powersetCard (Fin D) s) :
    (coordinateWedgeBasis D s).repr
      (exteriorPowerRep D s (diagGL t) (coordinateWedgeBasis D s A)) C =
        if C = A then ∏ i ∈ A.1, (t i : ℂ) else 0 := by
  classical
  rw [exteriorCoeff_eq_det]
  by_cases hCA : C = A
  · subst C
    have hmat : wedgeMinorMatrix D s (diagGL t) A A =
        Matrix.diagonal (fun i => (t ((Set.powersetCard.ofFinEmbEquiv.symm A) i) : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [wedgeMinorMatrix, diagGL, Matrix.diagonal_apply]
      · have hne : (Set.powersetCard.ofFinEmbEquiv.symm A) i ≠
            (Set.powersetCard.ofFinEmbEquiv.symm A) j := by
          intro h
          exact hij ((Set.powersetCard.ofFinEmbEquiv.symm A).injective h)
        simp [wedgeMinorMatrix, diagGL, Matrix.diagonal_apply, hij, Ne.symm hij, hne]
    rw [hmat, Matrix.det_diagonal]
    simpa using prod_embedding_eq_subset D s A fun i => (t i : ℂ)
  · obtain ⟨z, hzC, hzA⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne C A).mp hCA
    let eC := Set.powersetCard.ofFinEmbEquiv.symm C
    let eA := Set.powersetCard.ofFinEmbEquiv.symm A
    obtain ⟨k, hk⟩ := Set.mem_range.mp
      ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem C z).mpr hzC)
    have hk' : z = eC k := by simpa [eC] using hk.symm
    have hcol : ∀ i, wedgeMinorMatrix D s (diagGL t) A C i k = 0 := by
      intro i
      have hiA : eA i ∈ A :=
        (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A (eA i)).mp
          ⟨i, rfl⟩
      have hne : z ≠ eA i := by
        intro h
        apply hzA
        rw [h]
        exact hiA
      have hentry : eC k ≠ eA i := by
        intro h
        apply hne
        have h' : eC k = eA i := by simpa [eC, eA] using h
        calc
          z = eC k := hk'
          _ = eA i := h'
      change (Matrix.diagonal (fun j => (t j : ℂ))) (eC k) (eA i) = 0
      exact Matrix.diagonal_apply_ne _ hentry
    rw [Matrix.det_eq_zero_of_column_eq_zero k hcol]
    simp [hCA]

private noncomputable def interpUnit (j : Fin 3) : ℂˣ :=
  if j.val = 0 then 1 else if j.val = 1 then Units.mk0 2 (by norm_num) else
    Units.mk0 3 (by norm_num)

private noncomputable def interpCoeff (k j : Fin 3) : ℂ :=
  if k.val = 0 then
    if j.val = 0 then 3 else if j.val = 1 then -3 else 1
  else if k.val = 1 then
    if j.val = 0 then -(5 / 2 : ℂ) else if j.val = 1 then 4 else -(3 / 2 : ℂ)
  else if j.val = 0 then 1 / 2 else if j.val = 1 then -1 else 1 / 2

private theorem interpCoeff_eval (k m : Fin 3) :
    ∑ j : Fin 3, interpCoeff k j * (interpUnit j : ℂ) ^ m.val =
      if k = m then 1 else 0 := by
  classical
  fin_cases k <;> fin_cases m <;>
    norm_num [Fin.sum_univ_succ, interpCoeff, interpUnit, Units.val_mk0]

private noncomputable def pairWeight {D s : ℕ} (p : PairIdx D s s) (i : Fin D) : Fin 3 := by
  classical
  refine ⟨(if i ∈ p.1.1 then 1 else 0) + (if i ∈ p.2.1 then 1 else 0), ?_⟩
  by_cases hA : i ∈ p.1.1 <;> by_cases hB : i ∈ p.2.1 <;> simp [hA, hB] <;> omega

private noncomputable def highestWeightCoord (D s : ℕ) (hsD : s ≤ D) (i : Fin D) : Fin 3 := by
  classical
  refine ⟨if i ∈ (firstSubset D s hsD).1 then 2 else 0, ?_⟩
  split_ifs <;> omega

private noncomputable def pairEigenVal {D s : ℕ} (t : Fin D → ℂˣ)
    (p : PairIdx D s s) : ℂ :=
  (∏ i ∈ p.1.1, (t i : ℂ)) * ∏ i ∈ p.2.1, (t i : ℂ)

private theorem bigRep_basis_coeff (D s : ℕ) (g : GL (Fin D) ℂ)
    (p q : PairIdx D s s) :
    bigRep D s g (Pi.single p 1) q =
      ((coordinateWedgeBasis D s).repr
        (exteriorPowerRep D s g (coordinateWedgeBasis D s p.1)) q.1) *
      ((coordinateWedgeBasis D s).repr
        (exteriorPowerRep D s g (coordinateWedgeBasis D s p.2)) q.2) := by
  classical
  rcases q with ⟨qA, qB⟩
  have hp : (pairCoord D s s).symm (Pi.single p 1) = coordinateTensorBasis D s s p := by
    apply (pairCoord D s s).injective
    ext r
    simp [Pi.single_apply, pairCoord, coordinateTensorBasis]
  change (pairCoord D s s)
    (exteriorTensorRep D s g ((pairCoord D s s).symm (Pi.single p 1))) (qA, qB) = _
  rw [hp]
  simp [pairCoord, coordinateTensorBasis, exteriorTensorRep,
    Module.Basis.tensorProduct_apply', TensorProduct.map_tmul,
    Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul] <;> ring

private theorem bigRep_basis_coeff_transpose (D s : ℕ) (g : GL (Fin D) ℂ)
    (p q : PairIdx D s s) :
    bigRep D s (glTranspose g) (Pi.single q 1) p = bigRep D s g (Pi.single p 1) q := by
  rw [bigRep_basis_coeff, bigRep_basis_coeff, exteriorCoeff_transpose,
    exteriorCoeff_transpose]

private theorem bigRep_evalExpansion (D s : ℕ) (g : GL (Fin D) ℂ)
    (x : PairIdx D s s → ℂ) (q : PairIdx D s s) :
    bigRep D s g x q =
      ∑ p : PairIdx D s s, x p * bigRep D s g (Pi.single p 1) q := by
  classical
  have hexpansion (y : PairIdx D s s → ℂ) :
      y = ∑ p, y p • Pi.single p 1 := by
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using
      ((Pi.basisFun ℂ (PairIdx D s s)).sum_repr y).symm
  calc
    bigRep D s g x q =
        bigRep D s g (∑ p, x p • Pi.single p 1) q := by
          exact congrArg (fun y => bigRep D s g y q) (hexpansion x)
    _ = ∑ p : PairIdx D s s, x p * bigRep D s g (Pi.single p 1) q := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

private theorem bigRep_diag_basis_coeff (D s : ℕ) (t : Fin D → ℂˣ)
    (p q : PairIdx D s s) :
    bigRep D s (diagGL t) (Pi.single p 1) q =
      if p = q then pairEigenVal t p else 0 := by
  classical
  rcases p with ⟨pA, pB⟩
  rcases q with ⟨qA, qB⟩
  by_cases hA : qA = pA <;> by_cases hB : qB = pB
  · subst qA
    subst qB
    simp [bigRep_basis_coeff, exteriorCoeff_diagGL, pairEigenVal]
  · have hpq : (pA, pB) ≠ (qA, qB) := by
      intro h
      exact hB (congrArg Prod.snd h).symm
    have hcB : (coordinateWedgeBasis D s).repr
        (exteriorPowerRep D s (diagGL t) (coordinateWedgeBasis D s pB)) qB = 0 := by
      rw [exteriorCoeff_diagGL]
      simp [hB]
    rw [bigRep_basis_coeff, hcB, if_neg hpq]
    simp
  · have hpq : (pA, pB) ≠ (qA, qB) := by
      intro h
      exact hA (congrArg Prod.fst h).symm
    have hcA : (coordinateWedgeBasis D s).repr
        (exteriorPowerRep D s (diagGL t) (coordinateWedgeBasis D s pA)) qA = 0 := by
      rw [exteriorCoeff_diagGL]
      simp [hA]
    rw [bigRep_basis_coeff, hcA, if_neg hpq]
    simp
  · have hpq : (pA, pB) ≠ (qA, qB) := by
      intro h
      exact hA (congrArg Prod.fst h).symm
    have hcA : (coordinateWedgeBasis D s).repr
        (exteriorPowerRep D s (diagGL t) (coordinateWedgeBasis D s pA)) qA = 0 := by
      rw [exteriorCoeff_diagGL]
      simp [hA]
    rw [bigRep_basis_coeff, hcA, if_neg hpq]
    simp

private theorem bigRep_diag_apply (D s : ℕ) (t : Fin D → ℂˣ)
    (x : PairIdx D s s → ℂ) (q : PairIdx D s s) :
    bigRep D s (diagGL t) x q = x q * pairEigenVal t q := by
  classical
  rw [bigRep_evalExpansion]
  simp_rw [bigRep_diag_basis_coeff]
  simp

private theorem prod_subset_eq_prod_indicator {D : ℕ} (A : Finset (Fin D))
    (f : Fin D → ℂ) :
    (∏ i ∈ A, f i) = ∏ i, if i ∈ A then f i else 1 := by
  classical
  have hA : A = Finset.univ.filter (fun i : Fin D => i ∈ A) := by
    ext i
    simp
  rw [hA, Finset.prod_filter]
  simp

private theorem pairEigenVal_eq_weightProduct (D s : ℕ) (t : Fin D → ℂˣ)
    (p : PairIdx D s s) :
    pairEigenVal t p = ∏ i : Fin D, (t i : ℂ) ^ (pairWeight p i).val := by
  classical
  rw [pairEigenVal]
  have hA := prod_subset_eq_prod_indicator p.1.1 (fun i => (t i : ℂ))
  have hB := prod_subset_eq_prod_indicator p.2.1 (fun i => (t i : ℂ))
  rw [hA, hB, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hA : i ∈ p.1.1 <;> by_cases hB : i ∈ p.2.1 <;>
    simp [pairWeight, hA, hB, pow_two]

private theorem pairWeight_eq_highestWeightCoord_iff (D s : ℕ) (hsD : s ≤ D)
    (p : PairIdx D s s) :
    (∀ i, pairWeight p i = highestWeightCoord D s hsD i) ↔
      p = (firstSubset D s hsD, firstSubset D s hsD) := by
  classical
  constructor
  · intro h
    apply Prod.ext
    · apply Subtype.ext
      ext i
      have hval := congrArg Fin.val (h i)
      by_cases hi : i ∈ (firstSubset D s hsD).1
      · have hh : (if i ∈ p.1.1 then 1 else 0) + (if i ∈ p.2.1 then 1 else 0) = 2 := by
          simpa [pairWeight, highestWeightCoord, hi] using hval
        have hmem : i ∈ p.1.1 := by
          by_contra hnot
          by_cases hb : i ∈ p.2.1 <;> simp [hnot, hb] at hh <;> omega
        simp [hi, hmem]
      · have hh : (if i ∈ p.1.1 then 1 else 0) + (if i ∈ p.2.1 then 1 else 0) = 0 := by
          simpa [pairWeight, highestWeightCoord, hi] using hval
        have hnot : i ∉ p.1.1 := by
          by_contra ha
          by_cases hb : i ∈ p.2.1 <;> simp [ha, hb] at hh <;> omega
        simp [hi, hnot]
    · apply Subtype.ext
      ext i
      have hval := congrArg Fin.val (h i)
      by_cases hi : i ∈ (firstSubset D s hsD).1
      · have hh : (if i ∈ p.1.1 then 1 else 0) + (if i ∈ p.2.1 then 1 else 0) = 2 := by
          simpa [pairWeight, highestWeightCoord, hi] using hval
        have hmem : i ∈ p.2.1 := by
          by_contra hnot
          by_cases ha : i ∈ p.1.1 <;> simp [ha, hnot] at hh <;> omega
        simp [hi, hmem]
      · have hh : (if i ∈ p.1.1 then 1 else 0) + (if i ∈ p.2.1 then 1 else 0) = 0 := by
          simpa [pairWeight, highestWeightCoord, hi] using hval
        have hnot : i ∉ p.2.1 := by
          by_contra hb
          by_cases ha : i ∈ p.1.1 <;> simp [ha, hb] at hh <;> omega
        simp [hi, hnot]
  · rintro rfl i
    by_cases hi : i ∈ (firstSubset D s hsD).1
    · simp [pairWeight, highestWeightCoord, hi]
    · simp [pairWeight, highestWeightCoord, hi]

private theorem sum_univ_pi_prod {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Fintype (ι → κ)]
    (f : ι → κ → ℂ) :
    ∑ u : ι → κ, ∏ i, f i (u i) = ∏ i, ∑ j, f i j := by
  classical
  have hpi : Fintype.piFinset (fun _ : ι => (Finset.univ : Finset κ)) =
      (Finset.univ : Finset (ι → κ)) := by
    ext u
    simp
  calc
    ∑ u : ι → κ, ∏ i, f i (u i) =
        ∑ u ∈ (Finset.univ : Finset (ι → κ)), ∏ i, f i (u i) := by simp
    _ = ∑ u ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset κ)),
        ∏ i, f i (u i) := by rw [hpi]
    _ = ∏ i, ∑ j, f i j := by
      simpa using Finset.sum_prod_piFinset (ι := ι) (s := Finset.univ) (g := f)

private theorem torusProjectionScalar (D s : ℕ) (hsD : s ≤ D)
    (p : PairIdx D s s) :
    ∑ u : Fin D → Fin 3,
        (∏ i, interpCoeff (highestWeightCoord D s hsD i) (u i)) *
          pairEigenVal (fun i => interpUnit (u i)) p =
      if p = (firstSubset D s hsD, firstSubset D s hsD) then 1 else 0 := by
  classical
  have hterm (u : Fin D → Fin 3) :
      (∏ i, interpCoeff (highestWeightCoord D s hsD i) (u i)) *
          pairEigenVal (fun i => interpUnit (u i)) p =
        ∏ i, interpCoeff (highestWeightCoord D s hsD i) (u i) *
          (interpUnit (u i) : ℂ) ^ (pairWeight p i).val := by
    rw [pairEigenVal_eq_weightProduct]
    rw [← Finset.prod_mul_distrib]
  calc
    _ = ∑ u : Fin D → Fin 3,
        ∏ i, interpCoeff (highestWeightCoord D s hsD i) (u i) *
          (interpUnit (u i) : ℂ) ^ (pairWeight p i).val := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hterm u
    _ = ∏ i, ∑ j : Fin 3,
        interpCoeff (highestWeightCoord D s hsD i) j *
          (interpUnit j : ℂ) ^ (pairWeight p i).val := by
        exact sum_univ_pi_prod (fun i j =>
          interpCoeff (highestWeightCoord D s hsD i) j *
            (interpUnit j : ℂ) ^ (pairWeight p i).val)
    _ = ∏ i, if pairWeight p i = highestWeightCoord D s hsD i then 1 else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [interpCoeff_eval]
        by_cases h : pairWeight p i = highestWeightCoord D s hsD i
        · simp [h]
        · have h' : ¬highestWeightCoord D s hsD i = pairWeight p i := fun hh => h hh.symm
          simp [h, h']
    _ = if p = (firstSubset D s hsD, firstSubset D s hsD) then 1 else 0 := by
        by_cases hp : p = (firstSubset D s hsD, firstSubset D s hsD)
        · subst p
          have hwt : ∀ i, pairWeight (firstSubset D s hsD, firstSubset D s hsD) i =
              highestWeightCoord D s hsD i :=
            (pairWeight_eq_highestWeightCoord_iff D s hsD
              (firstSubset D s hsD, firstSubset D s hsD)).2 rfl
          simp [hwt]
        · have hdiff : ∃ i, pairWeight p i ≠ highestWeightCoord D s hsD i := by
            by_contra h
            have hall : ∀ i, pairWeight p i = highestWeightCoord D s hsD i := by
              intro i
              by_contra hi
              exact h ⟨i, hi⟩
            exact hp ((pairWeight_eq_highestWeightCoord_iff D s hsD p).mp hall)
          obtain ⟨i, hi⟩ := hdiff
          have hz : (if pairWeight p i = highestWeightCoord D s hsD i then (1 : ℂ) else 0) = 0 := by
            simp [hi]
          rw [Finset.prod_eq_zero (Finset.mem_univ i) hz]
          simp [hp]

private noncomputable def torusCoefficient (D s : ℕ) (hsD : s ≤ D)
    (u : Fin D → Fin 3) : ℂ :=
  ∏ i, interpCoeff (highestWeightCoord D s hsD i) (u i)

private noncomputable def torusProjection (D s : ℕ) (hsD : s ≤ D)
    (x : PairIdx D s s → ℂ) : PairIdx D s s → ℂ := by
  classical
  exact ∑ u : Fin D → Fin 3,
    torusCoefficient D s hsD u •
      bigRep D s (diagGL (fun i => interpUnit (u i))) x

private theorem torusProjection_eq (D s : ℕ) (hsD : s ≤ D)
    (x : PairIdx D s s → ℂ) :
    torusProjection D s hsD x =
      x (firstSubset D s hsD, firstSubset D s hsD) •
        highestVector D s hsD := by
  classical
  ext q
  simp only [torusProjection, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ u : Fin D → Fin 3,
        torusCoefficient D s hsD u *
          bigRep D s (diagGL (fun i => interpUnit (u i))) x q) =
      ∑ u, torusCoefficient D s hsD u *
        (x q * pairEigenVal (fun i => interpUnit (u i)) q) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [bigRep_diag_apply]
    _ = x q * ∑ u : Fin D → Fin 3,
        torusCoefficient D s hsD u * pairEigenVal (fun i => interpUnit (u i)) q := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu
          simp [torusCoefficient]
          ring
    _ = x q * (if q = (firstSubset D s hsD, firstSubset D s hsD) then 1 else 0) := by
          congr 1
          simpa only [torusCoefficient] using torusProjectionScalar D s hsD q
    _ = x (firstSubset D s hsD, firstSubset D s hsD) * highestVector D s hsD q := by
          by_cases hq : q = (firstSubset D s hsD, firstSubset D s hsD)
          · subst q
            simp [highestVector]
          · simp [highestVector, hq]

private theorem highestVector_ne_zero (D s : ℕ) (hsD : s ≤ D) :
    highestVector D s hsD ≠ 0 := by
  intro h
  have hz := congrFun h (firstSubset D s hsD, firstSubset D s hsD)
  norm_num [highestVector] at hz

private theorem highestVector_mem_ker (D s : ℕ) (hs : 1 ≤ s) (hsD : s ≤ D) :
    highestVector D s hsD ∈ LinearMap.ker (transferCoord D s) := by
  have hcyc := kernel_eq_span_orbit D s hs hsD
  have horbit : highestVector D s hsD ∈
      Set.range fun g : GL (Fin D) ℂ => bigRep D s g (highestVector D s hsD) := by
    exact ⟨1, by simp⟩
  rw [← hcyc]
  exact Submodule.subset_span horbit

private theorem kerRep_val (D s : ℕ) (hs : 1 ≤ s) (g : GL (Fin D) ℂ)
    (x : (kernelSubrep D s hs).toSubmodule) :
    ((kerRep D s hs) g x).val = bigRep D s g x.val := by
  rfl

private def coordinateBeta {D s : ℕ} (x y : PairIdx D s s → ℂ) : ℂ :=
  ∑ p, x p * y p

private theorem bigRep_transpose_adjoint (D s : ℕ) (g : GL (Fin D) ℂ)
    (x y : PairIdx D s s → ℂ) :
    coordinateBeta x (bigRep D s g y) =
      coordinateBeta (bigRep D s (glTranspose g) x) y := by
  classical
  simp only [coordinateBeta]
  calc
    (∑ p, x p * bigRep D s g y p) =
        ∑ p, ∑ q, x p * (y q * bigRep D s g (Pi.single q 1) p) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [bigRep_evalExpansion]
          simp [Finset.mul_sum, mul_assoc]
    _ = ∑ q, ∑ p, (x p * bigRep D s (glTranspose g) (Pi.single p 1) q) * y q := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          rw [← bigRep_basis_coeff_transpose D s g p q]
          ring
    _ = ∑ q, (∑ p, x p * bigRep D s (glTranspose g) (Pi.single p 1) q) * y q := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.sum_mul]
    _ = ∑ q, bigRep D s (glTranspose g) x q * y q := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [bigRep_evalExpansion]

private theorem exists_bigRep_orbit_pairing (D s : ℕ) (hs : 1 ≤ s) (hsD : s ≤ D)
    (w : PairIdx D s s → ℂ) (hw : w ≠ 0)
    (hker : transferCoord D s w = 0) :
    ∃ g : GL (Fin D) ℂ,
      ∑ p, w p * bigRep D s g (highestVector D s hsD) p ≠ 0 := by
  classical
  let wbar : PairIdx D s s → ℂ := fun p => star (w p)
  have hbarKer : transferCoord D s wbar = 0 := by
    calc
      transferCoord D s wbar = fun q => star (transferCoord D s w q) := by
        simpa [wbar] using transferCoord_conj D s w
      _ = 0 := by rw [hker]; ext q; simp
  have hbarMem : wbar ∈ LinearMap.ker (transferCoord D s) :=
    LinearMap.mem_ker.mpr hbarKer
  have hbarSpan : wbar ∈ Submodule.span ℂ
      (Set.range fun g : GL (Fin D) ℂ => bigRep D s g (highestVector D s hsD)) := by
    rw [← kernel_eq_span_orbit D s hs hsD] at hbarMem
    exact hbarMem
  let L : (PairIdx D s s → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun y => ∑ p, w p * y p
      map_add' := by
        intro y z
        simp [Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro a y
        simp [Finset.mul_sum, mul_assoc, mul_left_comm] }
  have hcoord : ∃ p, w p ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (funext fun p => h p)
  have hnormPos : 0 < ∑ p : PairIdx D s s, Complex.normSq (w p) := by
    refine Finset.sum_pos' ?_ ?_
    · intro p hp
      exact Complex.normSq_nonneg (w p)
    · obtain ⟨p, hp⟩ := hcoord
      exact ⟨p, Finset.mem_univ _, Complex.normSq_pos.mpr hp⟩
  have hpairNe : L wbar ≠ 0 := by
    intro hz
    have hre : Complex.re (L wbar) = ∑ p : PairIdx D s s, Complex.normSq (w p) := by
      simp [L, wbar, Complex.mul_conj]
    have hre0 := congrArg Complex.re hz
    rw [hre] at hre0
    simp at hre0
    linarith
  by_contra hno
  have horbitZero : ∀ g : GL (Fin D) ℂ,
      ∑ p, w p * bigRep D s g (highestVector D s hsD) p = 0 := by
    intro g
    by_contra hne
    exact hno ⟨g, hne⟩
  have hspanLe : Submodule.span ℂ
      (Set.range fun g : GL (Fin D) ℂ => bigRep D s g (highestVector D s hsD)) ≤
        LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro y ⟨g, rfl⟩
    change L (bigRep D s g (highestVector D s hsD)) = 0
    simpa [L] using horbitZero g
  have hLzero : L wbar = 0 := LinearMap.mem_ker.mp (hspanLe hbarSpan)
  exact hpairNe hLzero

theorem kerRep_irreducible (D s : ℕ) (hs : 1 ≤ s) (hsD : s ≤ D) :
    (kerRep D s hs).IsIrreducible := by
  classical
  change IsSimpleOrder (Subrepresentation (kerRep D s hs))
  let V := (kernelSubrep D s hs).toSubmodule
  let e₀ : PairIdx D s s := (firstSubset D s hsD, firstSubset D s hsD)
  let v₀ : V := ⟨highestVector D s hsD, highestVector_mem_ker D s hs hsD⟩
  have hbotTop : (⊥ : Subrepresentation (kerRep D s hs)) ≠ ⊤ := by
    intro h
    have hsub : (⊥ : Subrepresentation (kerRep D s hs)).toSubmodule = ⊤ := by
      have hh := congrArg Subrepresentation.toSubmodule h
      rw [show (⊤ : Subrepresentation (kerRep D s hs)).toSubmodule = ⊤ by rfl] at hh
      exact hh
    have hv : v₀ ∈ (⊥ : Subrepresentation (kerRep D s hs)).toSubmodule := by
      rw [hsub]
      simp
    have hz : v₀ = 0 := (Submodule.mem_bot ℂ).mp hv
    apply highestVector_ne_zero D s hsD
    exact congrArg Subtype.val hz
  haveI : Nontrivial (Subrepresentation (kerRep D s hs)) := ⟨⟨⊥, ⊤, hbotTop⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hS' : S.toSubmodule ≠ ⊥ := by
    intro h
    apply hS
    exact Subrepresentation.ext h
  obtain ⟨w, hwS, hwne⟩ := S.toSubmodule.ne_bot_iff.mp hS'
  have hwval : w.val ≠ 0 := by
    intro hz
    apply hwne
    exact Subtype.ext hz
  have hwker : transferCoord D s w.val = 0 := LinearMap.mem_ker.mp w.property
  obtain ⟨g, hpair⟩ := exists_bigRep_orbit_pairing D s hs hsD w.val hwval hwker
  let w' : V := (kerRep D s hs) (glTranspose g) w
  have hw'S : w' ∈ S.toSubmodule := by
    simpa [w'] using S.apply_mem_toSubmodule (glTranspose g) hwS
  have hw'val : w'.val = bigRep D s (glTranspose g) w.val := by
    simpa [w'] using kerRep_val D s hs (glTranspose g) w
  have hpair' : coordinateBeta w'.val (highestVector D s hsD) ≠ 0 := by
    have hadj : coordinateBeta w'.val (highestVector D s hsD) =
        coordinateBeta w.val (bigRep D s g (highestVector D s hsD)) := by
      rw [hw'val]
      exact (bigRep_transpose_adjoint D s g w.val (highestVector D s hsD)).symm
    rw [hadj]
    simpa [coordinateBeta] using hpair
  have hcoord : w'.val e₀ ≠ 0 := by
    have hbasis : coordinateBeta w'.val (highestVector D s hsD) = w'.val e₀ := by
      simp [coordinateBeta, highestVector, e₀, Pi.single_apply, Finset.sum_ite_eq']
    intro hz
    apply hpair'
    rw [hbasis, hz]
  let z : V := ∑ u : Fin D → Fin 3,
    torusCoefficient D s hsD u •
      (kerRep D s hs) (diagGL (fun i => interpUnit (u i))) w'
  have hzS : z ∈ S.toSubmodule := by
    simp only [z]
    apply Submodule.sum_mem
    intro u hu
    exact S.toSubmodule.smul_mem _
      (S.apply_mem_toSubmodule (diagGL (fun i => interpUnit (u i))) hw'S)
  have hzval : z.val = torusProjection D s hsD w'.val := by
    simp [z, torusProjection, kerRep, Subrepresentation.toRepresentation]
  have hzEq : z = (w'.val e₀) • v₀ := by
    apply Subtype.ext
    change z.val = (w'.val e₀) • highestVector D s hsD
    rw [hzval]
    simpa [e₀] using torusProjection_eq D s hsD w'.val
  have hscaled : (w'.val e₀) • v₀ ∈ S.toSubmodule := by
    rw [← hzEq]
    exact hzS
  have hv₀S : v₀ ∈ S.toSubmodule := by
    have hmul : (w'.val e₀)⁻¹ • ((w'.val e₀) • v₀) ∈ S.toSubmodule :=
      S.toSubmodule.smul_mem _ hscaled
    simpa [smul_smul, hcoord] using hmul
  let inc : V →ₗ[ℂ] (PairIdx D s s → ℂ) := (kernelSubrep D s hs).toSubmodule.subtype
  let imageS : Submodule ℂ (PairIdx D s s → ℂ) := Submodule.map inc S.toSubmodule
  have horbitImage (h : GL (Fin D) ℂ) :
      bigRep D s h (highestVector D s hsD) ∈ imageS := by
    rw [Submodule.mem_map]
    refine ⟨(kerRep D s hs) h v₀, S.apply_mem_toSubmodule h hv₀S, ?_⟩
    change ((kerRep D s hs) h v₀).val = bigRep D s h (highestVector D s hsD)
    rw [kerRep_val]
  have hkerLe : LinearMap.ker (transferCoord D s) ≤ imageS := by
    rw [← kernel_eq_span_orbit D s hs hsD]
    apply Submodule.span_le.mpr
    rintro y ⟨h, rfl⟩
    exact horbitImage h
  apply Subrepresentation.ext
  apply Submodule.eq_top_iff'.2
  intro x
  have hxker : x.val ∈ LinearMap.ker (transferCoord D s) := x.property
  have hximage : x.val ∈ imageS := hkerLe hxker
  rcases Submodule.mem_map.mp hximage with ⟨y, hyS, hyx⟩
  have hyx' : y = x := by
    apply Subtype.ext
    exact hyx
  rw [← hyx']
  exact hyS

theorem bigRep_zero_irreducible (D : ℕ) : (bigRep D 0).IsIrreducible := by
  classical
  change IsSimpleOrder (Subrepresentation (bigRep D 0))
  let i : PairIdx D 0 0 :=
    (⟨∅, by simp⟩, ⟨∅, by simp⟩)
  have : Subsingleton (PairIdx D 0 0) := ⟨fun x y => by
    rcases x with ⟨⟨A, hA⟩, ⟨B, hB⟩⟩
    rcases y with ⟨⟨C, hC⟩, ⟨E, hE⟩⟩
    have hA0 : A = ∅ := Finset.card_eq_zero.mp hA
    have hB0 : B = ∅ := Finset.card_eq_zero.mp hB
    have hC0 : C = ∅ := Finset.card_eq_zero.mp hC
    have hE0 : E = ∅ := Finset.card_eq_zero.mp hE
    subst A B C E
    rfl⟩
  have hbotTop : (⊥ : Subrepresentation (bigRep D 0)) ≠ ⊤ := by
    intro h
    have hmod : (⊥ : Subrepresentation (bigRep D 0)).toSubmodule = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    have hmem : (fun _ : PairIdx D 0 0 => (1 : ℂ)) ∈
        (⊥ : Submodule ℂ (PairIdx D 0 0 → ℂ)) := by
      change (fun _ : PairIdx D 0 0 => (1 : ℂ)) ∈
        (⊥ : Subrepresentation (bigRep D 0)).toSubmodule
      rw [hmod]
      simp
    have hzero : (fun _ : PairIdx D 0 0 => (1 : ℂ)) = 0 := (Submodule.mem_bot ℂ).mp hmem
    have hval := congrFun hzero i
    norm_num at hval
  have : Nontrivial (Subrepresentation (bigRep D 0)) := ⟨⟨⊥, ⊤, hbotTop⟩⟩
  refine ⟨?_⟩
  intro S
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · right
    apply Subrepresentation.ext
    apply Submodule.eq_top_iff'.2
    intro x
    have hS' : S.toSubmodule ≠ ⊥ := by
      intro h
      exact hS (Subrepresentation.ext h)
    obtain ⟨w, hwS, hw0⟩ := S.toSubmodule.ne_bot_iff.mp hS'
    have hcoord : w i ≠ 0 := by
      intro hz
      apply hw0
      funext j
      have hj : j = i := Subsingleton.elim _ _
      subst j
      exact hz
    have hx : x = (x i / w i) • w := by
      funext j
      have hj : j = i := Subsingleton.elim _ _
      subst j
      simp [hcoord]
    rw [hx]
    exact S.toSubmodule.smul_mem _ hwS

end Kraw
