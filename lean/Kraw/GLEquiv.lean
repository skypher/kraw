import Kraw.GLEquivAux

/-! `transferMap` is `GL`-equivariant (proof of Proposition 1.3, character part). -/

namespace Kraw

open scoped TensorProduct

theorem transferMap_equivariant (D s : ℕ) (hs : 1 ≤ s) (g : GL (Fin D) ℂ) :
    transferMap D s ∘ₗ exteriorTensorRep D s g =
        TensorProduct.map (exteriorPowerRep D (s + 1) g) (exteriorPowerRep D (s - 1) g) ∘ₗ
        transferMap D s := by
  simpa [exteriorTensorRep, exteriorPowerRep, standardRep] using
    (transferMap_natural D s hs (standardRep D g)).symm

end Kraw
