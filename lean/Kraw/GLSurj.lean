import Kraw.GLSurjAux

/-! `transferMap` is surjective (positivity of `E Eᵀ` on bidegree `(s+1, s-1)`). -/

namespace Kraw

theorem transferMap_surjective (D s : ℕ) (hs : 1 ≤ s) : Function.Surjective (transferMap D s) := by
  classical
  by_cases htarget : s + 1 ≤ D
  · exact GLSurjAux.transferMap_surjective_aux D s hs
  · have hfirst : IsEmpty (Set.powersetCard (Fin D) (s + 1)) := by
      refine ⟨fun A => ?_⟩
      have hcard : A.1.card ≤ (Finset.univ : Finset (Fin D)).card := Finset.card_le_univ A.1
      simp only [Finset.card_fin] at hcard
      have hA : A.1.card = s + 1 := A.2
      omega
    letI : IsEmpty
        (Set.powersetCard (Fin D) (s + 1) × Set.powersetCard (Fin D) (s - 1)) :=
      ⟨fun p => hfirst.false p.1⟩
    intro y
    refine ⟨0, ?_⟩
    let b := coordinateTensorBasis D (s + 1) (s - 1)
    apply b.equivFun.injective
    exact Subsingleton.elim _ _

end Kraw
