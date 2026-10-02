import Kraw.Schur

/-!
# Polynomial representations of `GL_n(ℂ)`

Paper Proposition 1.3 (character part), Macdonald, Ch. I, Appendix A: a representation is
polynomial if its matrix coefficients are polynomial functions of the matrix entries.
-/

open MvPolynomial

namespace Kraw

/-- The diagonal matrix with invertible entries `t`, as an element of `GL_n(ℂ)`. -/
noncomputable def diagGL {n : ℕ} (t : Fin n → ℂˣ) : GL (Fin n) ℂ where
  val := Matrix.diagonal fun i => (t i : ℂ)
  inv := Matrix.diagonal fun i => ((t i)⁻¹ : ℂˣ)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp

/-- The diagonal entries of `diag(I_M, -I_Q)`. -/
def zSignUnits (M Q : ℕ) : Fin (M + Q) → ℂˣ := fun i => if (i : ℕ) < M then 1 else -1

/-- A representation of `GL_n(ℂ)` is polynomial if, in some basis, every matrix coefficient
`g ↦ ⟨b_i^*, ρ(g) b_j⟩` is a polynomial function of the entries of `g`. -/
def IsPolynomialRep {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin n) ℂ) W) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℂ W), ∀ i j : ι,
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : GL (Fin n) ℂ,
      b.repr (ρ g (b j)) i =
        eval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) ℂ) ij.1 ij.2) P

end Kraw
