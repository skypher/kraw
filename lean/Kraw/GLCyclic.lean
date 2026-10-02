import Kraw.GLKernel
import Kraw.GLSurj
import Kraw.SchurJT
import Kraw.GLStdMono

/-! Cyclicity: `W = ker E` is spanned by the `GL`-orbit of `v₀`. -/

namespace Kraw

open exteriorPower
open scoped TensorProduct

private theorem subsetElem_firstSubset (D s : ℕ) (hD : s ≤ D)
    (k : Fin s) :
    subsetElem (firstSubset D s hD) k = Fin.castLE hD k := by
  let F : Finset (Fin D) := Finset.univ.filter (fun i => (i : ℕ) < s)
  have hcard : F.card = s := by
    dsimp [F]
    rw [Fin.card_filter_val_lt]
    omega
  have hEmb : (fun k : Fin s => Fin.castLE hD k) = F.orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique hcard
    · intro k
      simp [F]
    · intro a b hab
      exact hab
  change F.orderEmbOfFin _ k = Fin.castLE hD k
  rw [← hEmb]

private def firstColumns {D s : ℕ} (hD : s ≤ D) (g : GL (Fin D) ℂ) :
    Fin D × Fin s → ℂ :=
  fun ij => (g : Matrix (Fin D) (Fin D) ℂ) ij.1 (Fin.castLE hD ij.2)

private theorem eval_maxMinor_firstColumns {D s : ℕ} (hD : s ≤ D)
    (g : GL (Fin D) ℂ) (I : Set.powersetCard (Fin D) s) :
    MvPolynomial.eval (firstColumns hD g) (maxMinor I) =
      Matrix.det (Matrix.of fun k l : Fin s =>
        (g : Matrix (Fin D) (Fin D) ℂ) (subsetElem I k) (Fin.castLE hD l)) := by
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) (firstColumns hD g)
      (Matrix.det (Matrix.of fun k l : Fin s => MvPolynomial.X (subsetElem I k, l))) = _
  rw [RingHom.map_det]
  congr 1
  ext k l
  simp [firstColumns]

private theorem wedge_action_basis_repr {D s : ℕ} (hD : s ≤ D)
    (g : GL (Fin D) ℂ) (I : Set.powersetCard (Fin D) s) :
    (coordinateWedgeBasis D s).repr
      (exteriorPower.map s (standardRep D g) (coordinateWedgeBasis D s (firstSubset D s hD))) I =
        MvPolynomial.eval (firstColumns hD g) (maxMinor I) := by
  change ((Pi.basisFun ℂ (Fin D)).exteriorPower s).repr
      (exteriorPower.map s (standardRep D g)
        (((Pi.basisFun ℂ (Fin D)).exteriorPower s) (firstSubset D s hD))) I = _
  rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
    exteriorPower.basis_repr_apply, exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti]
  rw [eval_maxMinor_firstColumns]
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp [standardRep, Matrix.toLin'_apply, Pi.basisFun_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]
  change (g : Matrix (Fin D) (Fin D) ℂ) (subsetElem I i)
      (subsetElem (firstSubset D s hD) j) =
    (g : Matrix (Fin D) (Fin D) ℂ) (subsetElem I i) (Fin.castLE hD j)
  rw [subsetElem_firstSubset]

private theorem bigRep_highest_coordinate {D s : ℕ} (hD : s ≤ D)
    (g : GL (Fin D) ℂ) (A B : Set.powersetCard (Fin D) s) :
    bigRep D s g (highestVector D s hD) (A, B) =
      MvPolynomial.eval (firstColumns hD g) (maxMinor A * maxMinor B) := by
  have hvec : (pairCoord D s s).symm (highestVector D s hD) =
      coordinateTensorBasis D s s (firstSubset D s hD, firstSubset D s hD) := by
    apply (pairCoord D s s).injective
    simp [pairCoord, highestVector, coordinateTensorBasis]
  change ((pairCoord D s s)
      (TensorProduct.map (exteriorPower.map s (standardRep D g))
        (exteriorPower.map s (standardRep D g))
        ((pairCoord D s s).symm (highestVector D s hD)))) (A, B) = _
  rw [hvec]
  simp only [pairCoord, coordinateTensorBasis, Module.Basis.equivFun_apply,
    Module.Basis.tensorProduct_apply, TensorProduct.map_tmul,
    Module.Basis.tensorProduct_repr_tmul_apply]
  rw [wedge_action_basis_repr, wedge_action_basis_repr, MvPolynomial.eval_mul]
  ring

private theorem bigRep_highest_coordinate_pair {D s : ℕ} (hD : s ≤ D)
    (g : GL (Fin D) ℂ) (AB : PairIdx D s s) :
    bigRep D s g (highestVector D s hD) AB =
      MvPolynomial.eval (firstColumns hD g)
        (maxMinor AB.1 * maxMinor AB.2) := by
  rcases AB with ⟨A, B⟩
  exact bigRep_highest_coordinate hD g A B

private abbrev StandardPairs (D s : ℕ) :=
  {IJ : PairIdx D s s // IsStandardPair IJ.1 IJ.2}

private def orbitSpan (D s : ℕ) (hD : s ≤ D) : Submodule ℂ (PairIdx D s s → ℂ) :=
  Submodule.span ℂ (Set.range fun g : GL (Fin D) ℂ =>
    bigRep D s g (highestVector D s hD))

private def orbitCoordinate (D s : ℕ) (hD : s ≤ D) (IJ : StandardPairs D s) :
    Module.Dual ℂ (orbitSpan D s hD) :=
  (LinearMap.proj IJ.1).comp (orbitSpan D s hD).subtype

private theorem orbitCoordinates_linearIndependent (D s : ℕ) (hD : s ≤ D) :
    LinearIndependent ℂ (orbitCoordinate D s hD) := by
  classical
  rw [linearIndependent_iff']
  intro t c hlin IJ hIJ
  let P : MvPolynomial (Fin D × Fin s) ℂ :=
    ∑ IJ ∈ t, c IJ • (maxMinor IJ.1.1 * maxMinor IJ.1.2)
  have hEval (g : GL (Fin D) ℂ) :
      MvPolynomial.eval (firstColumns hD g) P = 0 := by
    have hmem : bigRep D s g (highestVector D s hD) ∈ orbitSpan D s hD :=
      Submodule.subset_span ⟨g, rfl⟩
    have hzero := DFunLike.congr_fun hlin ⟨bigRep D s g (highestVector D s hD), hmem⟩
    have heq : MvPolynomial.eval (firstColumns hD g) P =
        (∑ IJ ∈ t, c IJ • orbitCoordinate D s hD IJ)
          ⟨bigRep D s g (highestVector D s hD), hmem⟩ := by
      calc
        MvPolynomial.eval (firstColumns hD g) P =
            ∑ IJ ∈ t, c IJ * MvPolynomial.eval (firstColumns hD g)
              (maxMinor IJ.1.1 * maxMinor IJ.1.2) := by
          simp [P, MvPolynomial.smul_eval, MvPolynomial.eval_mul]
        _ = ∑ IJ ∈ t, c IJ • orbitCoordinate D s hD IJ
              ⟨bigRep D s g (highestVector D s hD), hmem⟩ := by
          apply Finset.sum_congr rfl
          intro IJ hIJ
          simp [orbitCoordinate, LinearMap.comp_apply, LinearMap.proj_apply,
            bigRep_highest_coordinate_pair, MvPolynomial.eval_mul, smul_eq_mul]
        _ = (∑ IJ ∈ t, c IJ • orbitCoordinate D s hD IJ)
              ⟨bigRep D s g (highestVector D s hD), hmem⟩ := by
          simp
    rw [heq]
    exact hzero
  let f : Fin D × Fin s → Fin D × Fin D := fun ij =>
    (ij.1, Fin.castLE hD ij.2)
  have hf : Function.Injective f := by
    intro x y hxy
    rcases x with ⟨xi, xj⟩
    rcases y with ⟨yi, yj⟩
    simp only [f, Prod.mk.injEq] at hxy
    have hxj : xj = yj := by
      apply Fin.ext
      simpa using congrArg Fin.val hxy.2
    exact Prod.ext hxy.1 hxj
  have hq : MvPolynomial.rename f P = 0 := by
    apply MvPolynomial.eq_of_eval_eq_on_gl
    intro g
    rw [MvPolynomial.eval_rename]
    change MvPolynomial.eval (firstColumns hD g) P = 0
    exact hEval g
  have hP : P = 0 := by
    apply MvPolynomial.rename_injective f hf
    simpa [MvPolynomial.rename_zero] using hq
  have hcoeff :=
    (linearIndependent_iff'.mp
      (maxMinor_products_linearIndependent D s)) t c hP IJ hIJ
  simpa using hcoeff

private theorem transferMap_diagonal_zero (D s : ℕ)
    (A : Set.powersetCard (Fin D) s) :
    transferMap D s (coordinateTensorBasis D s s (A, A)) = 0 := by
  rw [transferMap]
  simp only [Module.Basis.constr_basis]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hA : i ∈ A.1 <;> simp [hA]

private theorem transferCoord_highest_zero (D s : ℕ) (hD : s ≤ D) :
    transferCoord D s (highestVector D s hD) = 0 := by
  let A := firstSubset D s hD
  have hvec : (pairCoord D s s).symm (highestVector D s hD) =
      coordinateTensorBasis D s s (A, A) := by
    apply (pairCoord D s s).injective
    simp [A, pairCoord, highestVector, coordinateTensorBasis]
  change pairCoord D (s + 1) (s - 1)
    (transferMap D s ((pairCoord D s s).symm (highestVector D s hD))) = 0
  rw [hvec, transferMap_diagonal_zero]
  exact map_zero (pairCoord D (s + 1) (s - 1))

private theorem finrank_pairIdx (D k l : ℕ) :
    Module.finrank ℂ (PairIdx D k l → ℂ) = Nat.choose D k * Nat.choose D l := by
  rw [Module.finrank_pi]
  change Fintype.card (Set.powersetCard (Fin D) k × Set.powersetCard (Fin D) l) = _
  rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, Set.powersetCard.card,
    ← Nat.card_eq_fintype_card, Set.powersetCard.card]
  simp

private theorem transferCoord_surjective (D s : ℕ) (hs : 1 ≤ s) :
    Function.Surjective (transferCoord D s) := by
  intro y
  obtain ⟨x, hx⟩ := transferMap_surjective D s hs ((pairCoord D (s + 1) (s - 1)).symm y)
  refine ⟨pairCoord D s s x, ?_⟩
  change pairCoord D (s + 1) (s - 1)
    (transferMap D s ((pairCoord D s s).symm (pairCoord D s s x))) = y
  rw [LinearEquiv.symm_apply_apply, hx]
  exact LinearEquiv.apply_symm_apply _ y

private theorem transferCoord_ker_finrank (D s : ℕ) (hs : 1 ≤ s) :
    Module.finrank ℂ (LinearMap.ker (transferCoord D s)) =
      Nat.choose D s * Nat.choose D s - Nat.choose D (s + 1) * Nat.choose D (s - 1) := by
  have hrank := LinearMap.finrank_range_add_finrank_ker (transferCoord D s)
  have htop : LinearMap.range (transferCoord D s) = ⊤ :=
    LinearMap.range_eq_top.mpr (transferCoord_surjective D s hs)
  rw [htop, finrank_top, finrank_pairIdx, finrank_pairIdx] at hrank
  omega

theorem kernel_eq_span_orbit (D s : ℕ) (hs : 1 ≤ s) (hsD : s ≤ D) :
      Submodule.span ℂ (Set.range fun g : GL (Fin D) ℂ => bigRep D s g (highestVector D s hsD)) =
      LinearMap.ker (transferCoord D s) := by
  classical
  change orbitSpan D s hsD = LinearMap.ker (transferCoord D s)
  have hle : orbitSpan D s hsD ≤ LinearMap.ker (transferCoord D s) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    apply (kernelSubrep D s hs).apply_mem_toSubmodule g
    change highestVector D s hsD ∈ LinearMap.ker (transferCoord D s)
    rw [LinearMap.mem_ker]
    exact transferCoord_highest_zero D s hsD
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hli := orbitCoordinates_linearIndependent D s hsD
  have hcard : Fintype.card (StandardPairs D s) =
      Module.finrank ℂ (LinearMap.ker (transferCoord D s)) := by
    rw [card_standardPairs D s hs, transferCoord_ker_finrank D s hs]
    simp [pow_two]
  have hdimCoord : Fintype.card (StandardPairs D s) ≤
      Module.finrank ℂ (Module.Dual ℂ (orbitSpan D s hsD)) :=
    hli.fintype_card_le_finrank
  have hdimDual := hdimCoord.trans_eq Subspace.dual_finrank_eq
  have hdimKer : Module.finrank ℂ (LinearMap.ker (transferCoord D s)) ≤
      Module.finrank ℂ (orbitSpan D s hsD) := by
    rw [← hcard]
    exact hdimDual
  apply le_antisymm
  · exact Submodule.finrank_mono hle
  · exact hdimKer

end Kraw
