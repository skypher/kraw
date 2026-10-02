import Kraw.GLTrace
import Kraw.GLPoly
import Kraw.GLIrred
import Kraw.SchurProp

/-!
# Proposition 1.3: `Tur(s)` is an irreducible polynomial character value of `GL_D(ℂ)`
-/

open MvPolynomial

namespace Kraw

/-- Proposition 1.3 (character part): for `D ≥ 1` and `0 ≤ s ≤ D` there is an irreducible
polynomial representation of `GL_D(ℂ)` whose character on diagonal matrices is the Schur
polynomial `s_{(2^s)}`; its value at `diag(I_M, -I_Q)` is `Tur(s)`. -/
theorem tur_irreducible_character (M Q : ℕ) (hD : 1 ≤ M + Q) {s : ℕ} (hs : s ≤ M + Q) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (ρ : Representation ℂ (GL (Fin (M + Q)) ℂ) W),
      IsPolynomialRep ρ ∧ ρ.IsIrreducible ∧
        (∀ t : Fin (M + Q) → ℂˣ, LinearMap.trace ℂ W (ρ (diagGL t)) =
          eval (fun i => (t i : ℂ)) (map (Int.castRingHom ℂ) (schur (rect s) (M + Q)))) ∧
        LinearMap.trace ℂ W (ρ (diagGL (zSignUnits M Q))) = (Tur M Q s : ℂ) := by
  have hz : (fun i => ((zSignUnits M Q i : ℂˣ) : ℂ)) = fun i => ((zSign M Q i : ℤ) : ℂ) := by
    funext i
    simp only [zSignUnits, zSign]
    split_ifs <;> simp
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · refine ⟨PairIdx (M + Q) 0 0 → ℂ, inferInstance, inferInstance, inferInstance,
      bigRep (M + Q) 0, bigRep_zero_isPolynomial _, bigRep_zero_irreducible _, ?_, ?_⟩
    · intro t
      rw [trace_bigRep_zero]
      have h0 : schur (rect 0) (M + Q) = 1 := by
        have := schur_twoCol_zero (M + Q) 0
        simpa [rect] using this
      simp [h0]
    · rw [trace_bigRep_zero]
      have hT : Tur M Q 0 = 1 := by
        simp [Tur, p_zero, p_of_neg]
      simp [hT]
  · refine ⟨(kernelSubrep (M + Q) s hs1).toSubmodule, inferInstance, inferInstance, inferInstance,
      kerRep (M + Q) s hs1, kerRep_isPolynomial _ _ hs1, kerRep_irreducible _ _ hs1 hs, ?_, ?_⟩
    · intro t
      rw [trace_kerRep_diag, rect, schur_twoCol (M + Q) s s le_rfl hs1]
    · rw [trace_kerRep_diag, hz]
      have hp : ∀ r : ℕ, eval (fun i => ((zSign M Q i : ℤ) : ℂ))
          (MvPolynomial.map (Int.castRingHom ℂ) (esymm (Fin (M + Q)) ℤ r)) = (p M Q r : ℂ) := by
        intro r
        rw [MvPolynomial.eval_map, p_eq_esymm_zSign, MvPolynomial.eval]
        have h := MvPolynomial.eval₂_comp_left (Int.castRingHom ℂ) (RingHom.id ℤ) (zSign M Q)
          (esymm (Fin (M + Q)) ℤ r)
        rw [RingHom.comp_id] at h
        rw [MvPolynomial.coe_eval₂Hom]
        exact h.symm
      simp only [map_sub, map_mul, hp]
      have hsub : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by omega
      simp only [Tur, hsub]
      push_cast
      ring

end Kraw
