import Kraw.GLEquiv

/-!
# The representation `W = ker E` in coordinates

`Λ^s V ⊗ Λ^s V` is transported to its coordinate space `BigIdx D s → ℂ` (indexed by pairs of
`s`-subsets) along the tensor basis, so that submodules carry their standard instances.
-/

namespace Kraw

open scoped TensorProduct

/-- Pairs `(A, B)` of `k`- and `l`-subsets of `Fin D`. -/
abbrev PairIdx (D k l : ℕ) := Set.powersetCard (Fin D) k × Set.powersetCard (Fin D) l

/-- The coordinate equivalence of `Λ^k V ⊗ Λ^l V` given by the basis `e_A ⊗ e_B`. -/
noncomputable def pairCoord (D k l : ℕ) :
    ((⋀[ℂ]^k (Fin D → ℂ)) ⊗[ℂ] (⋀[ℂ]^l (Fin D → ℂ))) ≃ₗ[ℂ] (PairIdx D k l → ℂ) :=
  (coordinateTensorBasis D k l).equivFun

/-- The representation `Λ^s g ⊗ Λ^s g` in coordinates. -/
noncomputable def bigRep (D s : ℕ) : Representation ℂ (GL (Fin D) ℂ) (PairIdx D s s → ℂ) where
  toFun g := (pairCoord D s s).toLinearMap ∘ₗ exteriorTensorRep D s g ∘ₗ
    (pairCoord D s s).symm.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/-- `E` in coordinates. -/
noncomputable def transferCoord (D s : ℕ) :
    (PairIdx D s s → ℂ) →ₗ[ℂ] (PairIdx D (s + 1) (s - 1) → ℂ) :=
  (pairCoord D (s + 1) (s - 1)).toLinearMap ∘ₗ transferMap D s ∘ₗ (pairCoord D s s).symm.toLinearMap

/-- `W = ker E` as a subrepresentation. -/
noncomputable def kernelSubrep (D s : ℕ) (hs : 1 ≤ s) : Subrepresentation (bigRep D s) where
  toSubmodule := LinearMap.ker (transferCoord D s)
  apply_mem_toSubmodule g v hv := by
    rw [LinearMap.mem_ker] at hv ⊢
    have h := LinearMap.congr_fun (transferMap_equivariant D s hs g) ((pairCoord D s s).symm v)
    simp only [LinearMap.comp_apply] at h
    simp only [transferCoord, bigRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply] at hv ⊢
    rw [h]
    have hv' : transferMap D s ((pairCoord D s s).symm v) = 0 :=
      (pairCoord D (s + 1) (s - 1)).map_eq_zero_iff.mp hv
    rw [hv', map_zero, map_zero]

/-- The representation of `GL_D(ℂ)` on `W = ker E`. -/
noncomputable def kerRep (D s : ℕ) (hs : 1 ≤ s) :
    Representation ℂ (GL (Fin D) ℂ) (kernelSubrep D s hs).toSubmodule :=
  (kernelSubrep D s hs).toRepresentation

/-- The subset `{0, …, s-1}` of `Fin D`. -/
def firstSubset (D s : ℕ) (h : s ≤ D) : Set.powersetCard (Fin D) s :=
  ⟨Finset.univ.filter (fun i : Fin D => (i : ℕ) < s), by
    change (Finset.univ.filter (fun i : Fin D => (i : ℕ) < s)).card = s
    rw [Fin.card_filter_val_lt]
    omega⟩

/-- The highest weight vector `v₀ = e_{[s]} ⊗ e_{[s]}` in coordinates. -/
noncomputable def highestVector (D s : ℕ) (h : s ≤ D) : PairIdx D s s → ℂ :=
  Pi.single (firstSubset D s h, firstSubset D s h) 1

end Kraw
