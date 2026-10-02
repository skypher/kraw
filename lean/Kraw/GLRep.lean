import Kraw.GLDefs
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Exterior-power models for polynomial representations
-/

namespace Kraw

open exteriorPower
open scoped TensorProduct

/-- The standard representation of `GL (Fin D) ℂ` on coordinate vectors. -/
noncomputable def standardRep (D : ℕ) :
    Representation ℂ (GL (Fin D) ℂ) (Fin D → ℂ) where
  toFun g := Matrix.toLin' (g : Matrix (Fin D) (Fin D) ℂ)
  map_one' := by
    change Matrix.toLin' (1 : Matrix (Fin D) (Fin D) ℂ) = 1
    rw [Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    change Matrix.toLin' ((g : Matrix (Fin D) (Fin D) ℂ) *
      (h : Matrix (Fin D) (Fin D) ℂ)) = _
    rw [Matrix.toLin'_mul]
    rfl

/-- The representation induced on the `k`th exterior power of the standard module. -/
noncomputable def exteriorPowerRep (D k : ℕ) :
    Representation ℂ (GL (Fin D) ℂ) (⋀[ℂ]^k (Fin D → ℂ)) where
  toFun g := exteriorPower.map k (standardRep D g)
  map_one' := by
    change exteriorPower.map k (Matrix.toLin' (1 : Matrix (Fin D) (Fin D) ℂ)) = _
    rw [Matrix.toLin'_one, exteriorPower.map_id]
    rfl
  map_mul' g h := by
    change exteriorPower.map k
        (Matrix.toLin' ((g : Matrix (Fin D) (Fin D) ℂ) *
          (h : Matrix (Fin D) (Fin D) ℂ))) = _
    rw [Matrix.toLin'_mul, exteriorPower.map_comp]
    rfl

/-- The tensor square used for the rectangular character construction. -/
abbrev exteriorTensor (D s : ℕ) :=
  (⋀[ℂ]^s (Fin D → ℂ)) ⊗[ℂ] (⋀[ℂ]^s (Fin D → ℂ))

/-- The diagonal tensor action on the tensor square of an exterior power. -/
noncomputable def exteriorTensorRep (D s : ℕ) :
    Representation ℂ (GL (Fin D) ℂ) (exteriorTensor D s) where
  toFun g := TensorProduct.map (exteriorPowerRep D s g) (exteriorPowerRep D s g)
  map_one' := by
    apply TensorProduct.ext'
    intro x y
    simp [TensorProduct.map_tmul, exteriorPowerRep, standardRep, Matrix.toLin'_one]
  map_mul' g h := by
    apply TensorProduct.ext'
    intro x y
    simp only [TensorProduct.map_tmul, map_mul, Module.End.mul_apply]

/-- The basis of the `k`th exterior power induced by coordinate vectors. -/
noncomputable def coordinateWedgeBasis (D k : ℕ) :
    Module.Basis (Set.powersetCard (Fin D) k) ℂ (⋀[ℂ]^k (Fin D → ℂ)) :=
  (Pi.basisFun ℂ (Fin D)).exteriorPower k

/-- Tensor product basis for a pair of exterior powers. -/
noncomputable def coordinateTensorBasis (D k l : ℕ) :
    Module.Basis (Set.powersetCard (Fin D) k × Set.powersetCard (Fin D) l) ℂ
      ((⋀[ℂ]^k (Fin D → ℂ)) ⊗[ℂ] (⋀[ℂ]^l (Fin D → ℂ))) :=
  (coordinateWedgeBasis D k).tensorProduct (coordinateWedgeBasis D l)

/-- The sign from moving the `i`th coordinate past the earlier members of a wedge. -/
def wedgePositionSign {D : ℕ} (A : Finset (Fin D)) (i : Fin D) : ℂ :=
  (-1 : ℂ) ^ (A.filter fun j => j < i).card

/-- Insert a new coordinate into a fixed-cardinality subset. -/
def insertCoordinate {D s : ℕ} (A : Set.powersetCard (Fin D) s) (i : Fin D)
    (hi : i ∉ A.1) : Set.powersetCard (Fin D) (s + 1) :=
  ⟨insert i A.1, by
    change (insert i A.1).card = s + 1
    rw [Finset.card_insert_of_notMem hi, A.2]⟩

/-- Remove a coordinate from a fixed-cardinality subset. -/
def eraseCoordinate {D s : ℕ} (A : Set.powersetCard (Fin D) s) (i : Fin D)
    (hi : i ∈ A.1) : Set.powersetCard (Fin D) (s - 1) :=
  ⟨A.1.erase i, by
    change (A.1.erase i).card = s - 1
    rw [Finset.card_erase_of_mem hi, A.2]⟩

/-- The signed transfer map from bidegree `(s,s)` to `(s+1,s-1)`. -/
noncomputable def transferMap (D s : ℕ) :
    exteriorTensor D s →ₗ[ℂ]
      (⋀[ℂ]^(s + 1) (Fin D → ℂ)) ⊗[ℂ] (⋀[ℂ]^(s - 1) (Fin D → ℂ)) :=
  (coordinateTensorBasis D s s).constr ℂ fun AB =>
    ∑ i : Fin D,
      if hiA : i ∉ AB.1.1 then
        if hiB : i ∈ AB.2.1 then
          (wedgePositionSign AB.1.1 i * wedgePositionSign AB.2.1 i) •
            (coordinateWedgeBasis D (s + 1) (insertCoordinate AB.1 i hiA) ⊗ₜ[ℂ]
              coordinateWedgeBasis D (s - 1) (eraseCoordinate AB.2 i hiB))
        else 0
      else 0

private theorem transferMap_two_one_basis :
    transferMap 2 1
        ((coordinateTensorBasis 2 1 1)
          (⟨{0}, by simp⟩, ⟨{1}, by simp⟩)) =
      (-1 : ℂ) • ((coordinateWedgeBasis 2 2 ⟨{1, 0}, by simp⟩) ⊗ₜ[ℂ]
        coordinateWedgeBasis 2 0 ⟨∅, by simp⟩) := by
  rw [transferMap, coordinateTensorBasis]
  simp only [Module.Basis.constr_basis]
  simp [Fin.sum_univ_succ, wedgePositionSign, insertCoordinate, eraseCoordinate,
    coordinateWedgeBasis, Finset.filter_singleton]

end Kraw
