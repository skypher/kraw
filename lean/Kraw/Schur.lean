import Kraw.Defs

/-!
# Schur polynomials and two-column shapes

Paper Proposition 1.3.  Schur polynomials are defined combinatorially as generating functions
of semistandard Young tableaux (Macdonald, *Symmetric functions and Hall polynomials*, Ch. I,
(5.12)).  Cells of a `YoungDiagram` are pairs `(row, column)`.
-/

open MvPolynomial

namespace Kraw

/-- A filling `f` of the cells of `μ` with entries in `Fin n` is semistandard if rows weakly
increase from left to right and columns strictly increase from top to bottom. -/
def IsSemistandard {n : ℕ} (μ : YoungDiagram) (f : μ.cells → Fin n) : Prop :=
  (∀ a b : μ.cells, a.1.1 = b.1.1 → a.1.2 ≤ b.1.2 → f a ≤ f b) ∧
    (∀ a b : μ.cells, a.1.2 = b.1.2 → a.1.1 < b.1.1 → f a < f b)

open Classical in
/-- The Schur polynomial `s_μ(x_0, …, x_{n-1})`: the sum of `x^T` over semistandard tableaux `T`
of shape `μ` with entries in `Fin n`. -/
noncomputable def schur (μ : YoungDiagram) (n : ℕ) : MvPolynomial (Fin n) ℤ :=
  ∑ f ∈ Finset.univ.filter (fun f : μ.cells → Fin n => IsSemistandard μ f), ∏ c, X (f c)

/-- The Young diagram with two columns, of lengths `a ≥ b` (conjugate partition `(a, b)`). -/
def twoCol (a b : ℕ) (h : b ≤ a) : YoungDiagram where
  cells := Finset.range a ×ˢ {0} ∪ Finset.range b ×ˢ {1}
  isLowerSet := by
    intro x y hyx hx
    simp only [Finset.coe_union, Finset.coe_product, Finset.coe_range, Finset.coe_singleton,
      Set.mem_union, Set.mem_prod, Set.mem_Iio, Set.mem_singleton_iff] at hx ⊢
    obtain ⟨h1, h2⟩ := hyx
    rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
    · left; exact ⟨lt_of_le_of_lt h1 hx1, by omega⟩
    · rcases Nat.lt_or_ge y.2 1 with hy | hy
      · left; exact ⟨by omega, by omega⟩
      · right; exact ⟨lt_of_le_of_lt h1 hx1, by omega⟩

/-- The rectangle `(2^s)`: `s` rows of length `2`. -/
def rect (s : ℕ) : YoungDiagram := twoCol s s le_rfl

/-- The specialization `z = (1, …, 1, -1, …, -1)` with `M` ones and `Q` minus ones. -/
def zSign (M Q : ℕ) : Fin (M + Q) → ℤ := fun i => if (i : ℕ) < M then 1 else -1

end Kraw
