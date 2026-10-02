import Kraw.GLKernel

/-! Polynomiality of the representations `W = ker E` and `Λ^0 ⊗ Λ^0`. -/

namespace Kraw

open exteriorPower
open scoped TensorProduct

private noncomputable def minorPolynomial (D k : ℕ) (A B : Set.powersetCard (Fin D) k) :
    MvPolynomial (Fin D × Fin D) ℂ :=
  Matrix.det (Matrix.of fun i j : Fin k =>
    MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm A j,
      Set.powersetCard.ofFinEmbEquiv.symm B i))

private theorem eval_minorPolynomial (D k : ℕ) (A B : Set.powersetCard (Fin D) k)
    (g : GL (Fin D) ℂ) :
    MvPolynomial.eval (fun ij : Fin D × Fin D =>
      g.val ij.1 ij.2) (minorPolynomial D k A B) =
      Matrix.det (Matrix.of fun i j : Fin k =>
        g.val (Set.powersetCard.ofFinEmbEquiv.symm A j)
          (Set.powersetCard.ofFinEmbEquiv.symm B i)) := by
  simp [minorPolynomial, Matrix.det_apply]

private theorem exteriorPowerRep_coeff (D k : ℕ) (g : GL (Fin D) ℂ)
    (A B : Set.powersetCard (Fin D) k) :
    (coordinateWedgeBasis D k).repr
        (exteriorPowerRep D k g (coordinateWedgeBasis D k B)) A =
      MvPolynomial.eval (fun ij : Fin D × Fin D =>
        g.val ij.1 ij.2) (minorPolynomial D k A B) := by
  change ((Pi.basisFun ℂ (Fin D)).exteriorPower k).repr
      (exteriorPower.map k (Matrix.toLin' g.val)
        ((Pi.basisFun ℂ (Fin D)).exteriorPower k B)) A = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti, eval_minorPolynomial]
  simp [Pi.basisFun_repr, Matrix.toLin'_apply]

private noncomputable def bigRepCoeffPolynomial (D s : ℕ) (AB CD : PairIdx D s s) :
    MvPolynomial (Fin D × Fin D) ℂ :=
  minorPolynomial D s AB.1 CD.1 * minorPolynomial D s AB.2 CD.2

private theorem bigRep_coeff (D s : ℕ) (g : GL (Fin D) ℂ)
    (AB CD : PairIdx D s s) :
    (bigRep D s g (Pi.basisFun ℂ (PairIdx D s s) CD)) AB =
      MvPolynomial.eval (fun ij : Fin D × Fin D =>
        g.val ij.1 ij.2) (bigRepCoeffPolynomial D s AB CD) := by
  change (coordinateTensorBasis D s s).repr
      (TensorProduct.map (exteriorPowerRep D s g) (exteriorPowerRep D s g)
        ((coordinateTensorBasis D s s).equivFun.symm
          (Pi.basisFun ℂ (PairIdx D s s) CD))) AB = _
  have hinput : (coordinateTensorBasis D s s).equivFun.symm
      (Pi.basisFun ℂ (PairIdx D s s) CD) = coordinateTensorBasis D s s CD := by
    apply (coordinateTensorBasis D s s).equivFun.injective
    simp
  rw [hinput, coordinateTensorBasis]
  rw [Module.Basis.tensorProduct_apply', TensorProduct.map_tmul,
    Module.Basis.tensorProduct_repr_tmul_apply]
  rw [exteriorPowerRep_coeff, exteriorPowerRep_coeff]
  simp [bigRepCoeffPolynomial]
  ring

private theorem bigRep_isPolynomial (D s : ℕ) : IsPolynomialRep (bigRep D s) := by
  classical
  refine ⟨PairIdx D s s, inferInstance, Pi.basisFun ℂ (PairIdx D s s), ?_⟩
  intro AB CD
  refine ⟨bigRepCoeffPolynomial D s AB CD, ?_⟩
  intro g
  simpa [Pi.basisFun_repr] using bigRep_coeff D s g AB CD

private theorem linearFunctional_bigRep_isPolynomial (D s : ℕ)
    (L : (PairIdx D s s → ℂ) →ₗ[ℂ] ℂ) (v : PairIdx D s s → ℂ) :
    ∃ P : MvPolynomial (Fin D × Fin D) ℂ, ∀ g : GL (Fin D) ℂ,
      L (bigRep D s g v) = MvPolynomial.eval (fun ij : Fin D × Fin D =>
        g.val ij.1 ij.2) P := by
  classical
  let I := PairIdx D s s
  let b := Pi.basisFun ℂ I
  let P : MvPolynomial (Fin D × Fin D) ℂ :=
    ∑ AB : I, ∑ CD : I,
      MvPolynomial.C (L (b AB) * v CD) * bigRepCoeffPolynomial D s AB CD
  refine ⟨P, ?_⟩
  intro g
  have hdecomp (x : I → ℂ) : x = ∑ AB : I, x AB • b AB := by
    symm
    simpa [b, Pi.basisFun_repr] using (b.sum_repr x)
  have hcoord (AB : I) :
      (bigRep D s g v) AB = ∑ CD : I, v CD * (bigRep D s g (b CD)) AB := by
    calc
      (bigRep D s g v) AB =
          (bigRep D s g (∑ CD : I, v CD • b CD)) AB := by
            exact congrArg (fun x : I → ℂ => (bigRep D s g x) AB) (hdecomp v)
      _ = ∑ CD : I, v CD * (bigRep D s g (b CD)) AB := by
        simp [map_sum, map_smul, smul_eq_mul]
  have hL (x : I → ℂ) :
      L x = ∑ AB : I, L (b AB) * x AB := by
    calc
      L x = L (∑ AB : I, x AB • b AB) := congrArg L (hdecomp x)
      _ = ∑ AB : I, x AB * L (b AB) := by
        simp [map_sum, map_smul, smul_eq_mul]
      _ = ∑ AB : I, L (b AB) * x AB := by
        apply Finset.sum_congr rfl
        intro AB hAB
        ring
  calc
    L (bigRep D s g v) =
        ∑ AB : I, ∑ CD : I,
          (L (b AB) * v CD) * (bigRep D s g (b CD)) AB := by
      rw [hL]
      simp_rw [hcoord, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro AB hAB
      apply Finset.sum_congr rfl
      intro CD hCD
      ring
    _ = MvPolynomial.eval (fun ij : Fin D × Fin D =>
        g.val ij.1 ij.2) P := by
      simp only [P, MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
      apply Finset.sum_congr rfl
      intro AB hAB
      apply Finset.sum_congr rfl
      intro CD hCD
      simpa [b] using congrArg
        (fun z : ℂ => (L (b AB) * v CD) * z) (bigRep_coeff D s g AB CD)

theorem kerRep_isPolynomial (D s : ℕ) (hs : 1 ≤ s) : IsPolynomialRep (kerRep D s hs) := by
  classical
  let W := (kernelSubrep D s hs).toSubmodule
  let b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W := Module.finBasis ℂ W
  refine ⟨Fin (Module.finrank ℂ W), inferInstance, b, ?_⟩
  intro i j
  let f : W →ₗ[ℂ] ℂ := b.coord i
  obtain ⟨L, hL⟩ := LinearMap.exists_extend f
  let v : PairIdx D s s → ℂ := W.subtype (b j)
  obtain ⟨P, hP⟩ := linearFunctional_bigRep_isPolynomial D s L v
  refine ⟨P, ?_⟩
  intro g
  have hrestrict : W.subtype (kerRep D s hs g (b j)) = bigRep D s g v := rfl
  have hExt (x : W) : L (W.subtype x) = f x := by
    exact LinearMap.congr_fun hL x
  calc
    b.repr (kerRep D s hs g (b j)) i = f (kerRep D s hs g (b j)) := by
      simp [f]
    _ = L (W.subtype (kerRep D s hs g (b j))) := (hExt _).symm
    _ = L (bigRep D s g v) := by rw [hrestrict]
    _ = MvPolynomial.eval (fun ij : Fin D × Fin D =>
        g.val ij.1 ij.2) P := hP g

theorem bigRep_zero_isPolynomial (D : ℕ) : IsPolynomialRep (bigRep D 0) := by
  exact bigRep_isPolynomial D 0

end Kraw
