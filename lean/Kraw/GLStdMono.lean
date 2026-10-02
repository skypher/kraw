import Kraw.SchurJT
import Kraw.GLKernel
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Standard pairs and products of maximal minors (proof of cyclicity, Proposition 1.3)
-/

open MvPolynomial
open scoped MonomialOrder

namespace Kraw

/-- The `k`-th smallest element of an `s`-subset of `Fin D`. -/
noncomputable def subsetElem {D s : ℕ} (I : Set.powersetCard (Fin D) s) (k : Fin s) : Fin D :=
  I.1.orderEmbOfFin I.2 k

/-- Standard pairs `I ≤ J` componentwise: the semistandard tableaux of shape `(2^s)`. -/
def IsStandardPair {D s : ℕ} (I J : Set.powersetCard (Fin D) s) : Prop :=
  ∀ k : Fin s, subsetElem I k ≤ subsetElem J k

/-- The maximal minor `det Y_I` of the `D × s` matrix of indeterminates `Y_{i,l} = X (i,l)`. -/
noncomputable def maxMinor {D s : ℕ} (I : Set.powersetCard (Fin D) s) :
    MvPolynomial (Fin D × Fin s) ℂ :=
  Matrix.det (Matrix.of fun k l : Fin s => X (subsetElem I k, l))

@[instance_reducible] private noncomputable def minorVariableOrder (D s : ℕ) :
    LinearOrder (Fin D × Fin s) :=
  LinearOrder.lift' (fun p : Fin D × Fin s => toLex (p.2, p.1)) (by
    intro a b h
    have h' := toLex_inj.mp h
    exact Prod.ext (congrArg Prod.snd h') (congrArg Prod.fst h'))

@[instance_reducible] private def minorVariableLT (D s : ℕ) : LT (Fin D × Fin s) :=
  ⟨fun p q => toLex (p.2, p.1) < toLex (q.2, q.1)⟩

private noncomputable def minorMonomialOrder (D s : ℕ) :
    MonomialOrder (Fin D × Fin s) := by
  letI : LinearOrder (Fin D × Fin s) := minorVariableOrder D s
  letI : LT (Fin D × Fin s) := minorVariableLT D s
  letI : IsTrans (Fin D × Fin s) (· > ·) := ⟨fun (a b c : Fin D × Fin s) hab hbc => by
    change toLex (b.2, b.1) < toLex (a.2, a.1) at hab
    change toLex (c.2, c.1) < toLex (b.2, b.1) at hbc
    change toLex (c.2, c.1) < toLex (a.2, a.1)
    exact lt_trans hbc hab⟩
  letI : Std.Irrefl (· > ·) := ⟨fun (a : Fin D × Fin s) ha => by
    change toLex (a.2, a.1) < toLex (a.2, a.1) at ha
    exact lt_irrefl _ ha⟩
  letI : WellFoundedGT (Fin D × Fin s) :=
    ⟨Finite.wellFounded_of_trans_of_irrefl (· > ·)⟩
  exact @MonomialOrder.lex (Fin D × Fin s) (minorVariableOrder D s) ‹WellFoundedGT (Fin D × Fin s)›

private noncomputable def diagonalExponent {D s : ℕ} (I : Set.powersetCard (Fin D) s) :
    (Fin D × Fin s) →₀ ℕ :=
  ∑ k : Fin s, Finsupp.single (subsetElem I k, k) 1

private noncomputable def permutationExponent {D s : ℕ} (I : Set.powersetCard (Fin D) s)
    (σ : Equiv.Perm (Fin s)) : (Fin D × Fin s) →₀ ℕ :=
  ∑ k : Fin s, Finsupp.single (subsetElem I (σ k), k) 1

private lemma diagonalExponent_apply {D s : ℕ} (I : Set.powersetCard (Fin D) s)
    (r : Fin D) (c : Fin s) : diagonalExponent I (r, c) =
      if r = subsetElem I c then 1 else 0 := by
  classical
  rw [diagonalExponent, Finset.sum_apply']
  rw [Finset.sum_eq_single c]
  · simp [Finsupp.single_apply, eq_comm]
  · intro k hk hkc
    simp [Finsupp.single_apply, hkc]
  · simp

private lemma permutationExponent_apply {D s : ℕ} (I : Set.powersetCard (Fin D) s)
    (σ : Equiv.Perm (Fin s)) (r : Fin D) (c : Fin s) :
    permutationExponent I σ (r, c) = if r = subsetElem I (σ c) then 1 else 0 := by
  classical
  rw [permutationExponent, Finset.sum_apply']
  rw [Finset.sum_eq_single c]
  · simp [Finsupp.single_apply, eq_comm]
  · intro k hk hkc
    simp [Finsupp.single_apply, hkc]
  · simp

private lemma permutationExponent_lt_diagonal {D s : ℕ}
    (I : Set.powersetCard (Fin D) s) (σ : Equiv.Perm (Fin s)) (hσ : σ ≠ 1) :
    permutationExponent I σ ≺[minorMonomialOrder D s] diagonalExponent I := by
  classical
  letI : LinearOrder (Fin D × Fin s) := minorVariableOrder D s
  letI : LT (Fin D × Fin s) := minorVariableLT D s
  let moved : Finset (Fin s) := Finset.univ.filter fun k => σ k ≠ k
  have hmoved : moved.Nonempty := by
    by_contra h
    apply hσ
    ext k
    by_contra hk
    have hk' : σ k ≠ k := by
      intro heq
      exact hk (congrArg Fin.val heq)
    exact h ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩⟩
  let i : Fin s := moved.min' hmoved
  have hi : σ i ≠ i := (Finset.mem_filter.mp (moved.min'_mem hmoved)).2
  have hfixed : ∀ j : Fin s, j < i → σ j = j := by
    intro j hji
    by_contra hj
    have hj' : σ j ≠ j := hj
    have hjm : j ∈ moved := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩
    exact (not_le_of_gt hji) (moved.min'_le j hjm)
  have hlt : i < σ i := by
    rcases lt_trichotomy (σ i) i with hlt | heq | hgt
    · have hfix := hfixed (σ i) hlt
      exact (hi (σ.injective hfix)).elim
    · exact (hi heq).elim
    · exact hgt
  have hrow : subsetElem I i < subsetElem I (σ i) :=
    (I.1.orderEmbOfFin I.2).strictMono hlt
  change toLex (permutationExponent I σ) < toLex (diagonalExponent I)
  rw [Finsupp.Lex.lt_iff]
  refine ⟨(subsetElem I i, i), ?_, ?_⟩
  · intro y hy
    change toLex (y.2, y.1) < toLex (i, subsetElem I i) at hy
    rcases Prod.Lex.toLex_lt_toLex.mp hy with hycol | ⟨hcol, hyrow⟩
    · change permutationExponent I σ y = diagonalExponent I y
      rw [permutationExponent_apply, diagonalExponent_apply]
      simp [hfixed y.2 hycol]
    · change permutationExponent I σ y = diagonalExponent I y
      change y.2 = i at hcol
      have hcol' : y.2 = i := hcol
      rw [permutationExponent_apply, diagonalExponent_apply, hcol']
      have h₁ : y.1 ≠ subsetElem I (σ i) := ne_of_lt (lt_trans hyrow hrow)
      have h₂ : y.1 ≠ subsetElem I i := ne_of_lt hyrow
      simp [h₁, h₂]
  · change permutationExponent I σ (subsetElem I i, i) <
      diagonalExponent I (subsetElem I i, i)
    rw [permutationExponent_apply, diagonalExponent_apply]
    simp [hrow.ne]

private lemma permutationExponent_le_diagonal {D s : ℕ}
    (I : Set.powersetCard (Fin D) s) (σ : Equiv.Perm (Fin s)) :
    permutationExponent I σ ≼[minorMonomialOrder D s] diagonalExponent I := by
  by_cases hσ : σ = 1
  · subst σ
    simp [permutationExponent, diagonalExponent]
  · exact le_of_lt (permutationExponent_lt_diagonal I σ hσ)

private noncomputable def minorPermutationProduct {D s : ℕ}
    (I : Set.powersetCard (Fin D) s) (σ : Equiv.Perm (Fin s)) :
    MvPolynomial (Fin D × Fin s) ℂ :=
  ∏ k : Fin s, X (subsetElem I (σ k), k)

private noncomputable def minorPermutationTerm {D s : ℕ}
    (I : Set.powersetCard (Fin D) s) (σ : Equiv.Perm (Fin s)) :
    MvPolynomial (Fin D × Fin s) ℂ :=
  C ((Equiv.Perm.sign σ : ℤ) : ℂ) * minorPermutationProduct I σ

private lemma minorPermutationProduct_degree {D s : ℕ}
    (I : Set.powersetCard (Fin D) s) (σ : Equiv.Perm (Fin s)) :
    (minorMonomialOrder D s).degree (minorPermutationProduct I σ) =
      permutationExponent I σ := by
  classical
  simp [minorPermutationProduct, permutationExponent,
    MonomialOrder.degree_prod, MonomialOrder.degree_X]

private lemma minorPermutationTerm_degree_le {D s : ℕ}
    (I : Set.powersetCard (Fin D) s) (σ : Equiv.Perm (Fin s)) :
    (minorMonomialOrder D s).degree (minorPermutationTerm I σ) ≼[minorMonomialOrder D s]
      permutationExponent I σ := by
  change (minorMonomialOrder D s).degree
      (C ((Equiv.Perm.sign σ : ℤ) : ℂ) * minorPermutationProduct I σ) ≼[
        minorMonomialOrder D s] permutationExponent I σ
  rw [← smul_eq_C_mul]
  change (minorMonomialOrder D s).degree
      (((Equiv.Perm.sign σ : ℤ) : ℂ) • minorPermutationProduct I σ) ≼[
        minorMonomialOrder D s] permutationExponent I σ
  rw [← minorPermutationProduct_degree I σ]
  exact (minorMonomialOrder D s).degree_smul_le

private lemma maxMinor_degree_and_leadingCoeff {D s : ℕ}
    (I : Set.powersetCard (Fin D) s) :
    (minorMonomialOrder D s).degree (maxMinor I) = diagonalExponent I ∧
      (minorMonomialOrder D s).leadingCoeff (maxMinor I) = 1 := by
  classical
  let m := minorMonomialOrder D s
  let f := fun σ : Equiv.Perm (Fin s) => minorPermutationTerm I σ
  have hdet : maxMinor I = ∑ σ : Equiv.Perm (Fin s), f σ := by
    simp [maxMinor, f, minorPermutationTerm, minorPermutationProduct, Matrix.det_apply']
  have hterm : ∀ σ, σ ≠ 1 → m.degree (f σ) ≺[m] diagonalExponent I := by
    intro σ hσ
    calc
      m.degree (f σ) ≼[m] permutationExponent I σ := minorPermutationTerm_degree_le I σ
      _ ≺[m] diagonalExponent I := permutationExponent_lt_diagonal I σ hσ
  have hcoeff : (maxMinor I).coeff (diagonalExponent I) = 1 := by
    have hcoeffdet := congrArg (fun p : MvPolynomial (Fin D × Fin s) ℂ =>
      p.coeff (diagonalExponent I)) hdet
    simp only [f, coeff_sum] at hcoeffdet
    rw [hcoeffdet, Finset.sum_eq_single (1 : Equiv.Perm (Fin s))]
    · have hp := (m.coeff_prod_sum_degree
        (fun k : Fin s => (X (subsetElem I k, k) :
          MvPolynomial (Fin D × Fin s) ℂ)) Finset.univ)
      simpa [minorPermutationProduct, diagonalExponent, MonomialOrder.degree_X,
        minorPermutationTerm, Equiv.Perm.sign_one] using hp
    · intro σ hσmem hσne
      rw [m.coeff_eq_zero_of_lt (hterm σ (by simpa using hσne))]
    · simp
  have hupper : m.toSyn (m.degree (maxMinor I)) ≤ m.toSyn (diagonalExponent I) := by
    rw [hdet]
    calc
      m.toSyn (m.degree (∑ σ : Equiv.Perm (Fin s), f σ)) ≤
          Finset.univ.sup (fun σ : Equiv.Perm (Fin s) => m.toSyn (m.degree (f σ))) := by
        simpa using (m.degree_sum_le (s := Finset.univ) (f := f))
      _ ≤ m.toSyn (diagonalExponent I) := by
        apply Finset.sup_le_iff.mpr
        intro σ hσmem
        exact (minorPermutationTerm_degree_le I σ).trans
          (permutationExponent_le_diagonal I σ)
  have hdegree : m.degree (maxMinor I) = diagonalExponent I := by
    apply m.toSyn.injective
    apply le_antisymm hupper
    apply m.le_degree
    rw [MvPolynomial.mem_support_iff, hcoeff]
    exact one_ne_zero
  refine ⟨hdegree, ?_⟩
  rw [MonomialOrder.leadingCoeff, hdegree]
  exact hcoeff

private lemma maxMinor_degree {D s : ℕ} (I : Set.powersetCard (Fin D) s) :
    (minorMonomialOrder D s).degree (maxMinor I) = diagonalExponent I :=
  (maxMinor_degree_and_leadingCoeff I).1

private lemma maxMinor_leadingCoeff {D s : ℕ} (I : Set.powersetCard (Fin D) s) :
    (minorMonomialOrder D s).leadingCoeff (maxMinor I) = 1 :=
  (maxMinor_degree_and_leadingCoeff I).2

private lemma maxMinor_ne_zero {D s : ℕ} (I : Set.powersetCard (Fin D) s) :
    maxMinor I ≠ 0 := by
  apply (minorMonomialOrder D s).leadingCoeff_ne_zero_iff.mp
  simp [maxMinor_leadingCoeff]

private lemma maxMinor_product_degree {D s : ℕ}
    (I J : Set.powersetCard (Fin D) s) :
    (minorMonomialOrder D s).degree (maxMinor I * maxMinor J) =
      diagonalExponent I + diagonalExponent J := by
  rw [(minorMonomialOrder D s).degree_mul (maxMinor_ne_zero I) (maxMinor_ne_zero J),
    maxMinor_degree, maxMinor_degree]

private lemma maxMinor_product_leadingCoeff {D s : ℕ}
    (I J : Set.powersetCard (Fin D) s) :
    (minorMonomialOrder D s).leadingCoeff (maxMinor I * maxMinor J) = 1 := by
  rw [(minorMonomialOrder D s).leadingCoeff_mul,
    maxMinor_leadingCoeff, maxMinor_leadingCoeff]
  norm_num

private lemma sortedRows_eq_of_counts {D : ℕ} {a b c d : Fin D}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hcounts : ∀ r : Fin D,
      (if r = a then 1 else 0) + (if r = b then 1 else 0) =
        (if r = c then 1 else 0) + (if r = d then 1 else 0)) :
    a = c ∧ b = d := by
  by_cases hab' : a = b
  · subst b
    have h := hcounts a
    have h' : (2 : ℕ) = (if a = c then 1 else 0) + (if a = d then 1 else 0) := by
      simpa using h
    by_cases hac : a = c
    · by_cases had : a = d
      · exact ⟨hac, had⟩
      · rw [if_pos hac, if_neg had] at h'
        norm_num at h'
    · by_cases had : a = d
      · rw [if_neg hac, if_pos had] at h'
        norm_num at h'
      · have hfalse : (2 : ℕ) = 0 := by
          rw [if_neg hac, if_neg had] at h'
          exact h'
        omega
  · have hlt : a < b := lt_of_le_of_ne hab hab'
    have hleft : a = c := by
      by_contra hac
      have ha := hcounts a
      have had : a = d := by
        have ha' : (1 : ℕ) = if a = d then 1 else 0 := by
          simpa [hlt.ne, hac] using ha
        by_contra hnot
        simp [hnot] at ha'
      have hca : c ≤ a := by simpa [had] using hcd
      have hca' : c < a := lt_of_le_of_ne hca (Ne.symm hac)
      have hcb : c < b := lt_trans hca' hlt
      have hb := hcounts b
      have hbc : b ≠ c := ne_of_gt hcb
      have hbd : b ≠ d := by simpa [had] using hlt.ne.symm
      have hfalse : False := by simpa [hlt.ne.symm, hbc, hbd] using hb
      exact hfalse.elim
    have hright : b = d := by
      have hb := hcounts b
      have hbc : b ≠ c := by simpa [hleft] using hlt.ne.symm
      have hbd : (1 : ℕ) = if b = d then 1 else 0 := by
        simpa [hlt.ne.symm, hbc] using hb
      by_cases hbd' : b = d
      · exact hbd'
      · simp [hbd'] at hbd
    exact ⟨hleft, hright⟩

private lemma standardPairExponent_injective {D s : ℕ}
    {I J I' J' : Set.powersetCard (Fin D) s}
    (hIJ : IsStandardPair I J) (hI'J' : IsStandardPair I' J')
    (h : diagonalExponent I + diagonalExponent J =
      diagonalExponent I' + diagonalExponent J') : I = I' ∧ J = J' := by
  classical
  have hrows (k : Fin s) : subsetElem I k = subsetElem I' k ∧
      subsetElem J k = subsetElem J' k := by
    apply sortedRows_eq_of_counts (hIJ k) (hI'J' k)
    intro r
    have hr := congrArg (fun e : (Fin D × Fin s) →₀ ℕ => e (r, k)) h
    simpa [Finsupp.add_apply, diagonalExponent_apply] using hr
  have hembI : I.1.orderEmbOfFin I.2 = I'.1.orderEmbOfFin I'.2 := by
    apply RelEmbedding.ext
    intro k
    exact (hrows k).1
  have hembJ : J.1.orderEmbOfFin J.2 = J'.1.orderEmbOfFin J'.2 := by
    apply RelEmbedding.ext
    intro k
    exact (hrows k).2
  have hfinI : I.1 = I'.1 := by
    calc
      I.1 = Finset.image (I.1.orderEmbOfFin I.2) Finset.univ :=
        (Finset.image_orderEmbOfFin_univ I.1 I.2).symm
      _ = Finset.image (I'.1.orderEmbOfFin I'.2) Finset.univ := by rw [hembI]
      _ = I'.1 := Finset.image_orderEmbOfFin_univ I'.1 I'.2
  have hfinJ : J.1 = J'.1 := by
    calc
      J.1 = Finset.image (J.1.orderEmbOfFin J.2) Finset.univ :=
        (Finset.image_orderEmbOfFin_univ J.1 J.2).symm
      _ = Finset.image (J'.1.orderEmbOfFin J'.2) Finset.univ := by rw [hembJ]
      _ = J'.1 := Finset.image_orderEmbOfFin_univ J'.1 J'.2
  exact ⟨Subtype.ext hfinI, Subtype.ext hfinJ⟩

private theorem linearIndependent_of_distinct_degree {ι σ : Type*} {R : Type*}
    [Field R] (m : MonomialOrder σ) (p : ι → MvPolynomial σ R)
    (hdegree : ∀ i j, m.degree (p i) = m.degree (p j) → i = j)
    (hlc : ∀ i, m.leadingCoeff (p i) = 1) : LinearIndependent R p := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  by_contra hci
  let active : Finset ι := s.filter fun j => c j ≠ 0
  have hactive : active.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
  obtain ⟨j, hjactive, hjmax⟩ := Finset.exists_max_image active
    (fun j => m.toSyn (m.degree (p j))) hactive
  have hjs : j ∈ s := (Finset.mem_filter.mp hjactive).1
  have hcj : c j ≠ 0 := (Finset.mem_filter.mp hjactive).2
  have hcoeffsum :
      (∑ k ∈ s, c k • p k).coeff (m.degree (p j)) =
        c j * m.leadingCoeff (p j) := by
    rw [coeff_sum, Finset.sum_eq_single j]
    · simp [coeff_smul, smul_eq_mul, MonomialOrder.leadingCoeff]
    · intro k hk hkj
      by_cases hck : c k = 0
      · simp [hck]
      · have hkactive : k ∈ active := Finset.mem_filter.mpr ⟨hk, hck⟩
        have hkmax : m.toSyn (m.degree (p k)) ≤ m.toSyn (m.degree (p j)) :=
          hjmax k hkactive
        have hne : m.toSyn (m.degree (p k)) ≠ m.toSyn (m.degree (p j)) := by
          intro heq
          exact hkj (hdegree k j (m.toSyn.injective heq))
        have hlt : m.degree (p k) ≺[m] m.degree (p j) := lt_of_le_of_ne hkmax hne
        rw [coeff_smul, m.coeff_eq_zero_of_lt hlt]
        simp
    · intro hjnot
      exact (hjnot hjs).elim
  have hcoeffzero : (∑ k ∈ s, c k • p k).coeff (m.degree (p j)) = 0 := by
    rw [hsum]
    simp
  rw [hcoeffsum, hlc j] at hcoeffzero
  exact hcj (by simpa using hcoeffzero)

private lemma rectCellCoordinates (s : ℕ) (c : {c // c ∈ rect s}) :
    c.1.1 < s ∧ (c.1.2 = 0 ∨ c.1.2 = 1) := by
  have hc : (∃ a < s, (a, 0) = c.1) ∨ ∃ a < s, (a, 1) = c.1 := by
    simpa [rect, twoCol] using c.2
  rcases hc with ⟨a, ha, hEq⟩ | ⟨a, ha, hEq⟩
  · constructor
    · have h := congrArg Prod.fst hEq
      omega
    · exact Or.inl (congrArg Prod.snd hEq).symm
  · constructor
    · have h := congrArg Prod.fst hEq
      omega
    · exact Or.inr (congrArg Prod.snd hEq).symm

private def rectCellsEquiv (s : ℕ) : (Fin s × Bool) ≃ {c // c ∈ rect s} where
  toFun x := ⟨(x.1.1, if x.2 then 1 else 0), by
    cases x.2 <;> simp [rect, twoCol]
  ⟩
  invFun c := (⟨c.1.1, (rectCellCoordinates s c).1⟩, decide (c.1.2 = 1))
  left_inv x := by
    rcases x with ⟨i, b⟩
    cases b <;> rfl
  right_inv c := by
    apply Subtype.ext
    rcases (rectCellCoordinates s c).2 with h | h
    · apply Prod.ext <;> simp [h]
    · apply Prod.ext <;> simp [h]

private def rectFunctionEquiv (s D : ℕ) :
    ((rect s).cells → Fin D) ≃ (Fin s → Bool → Fin D) where
  toFun f i b := f (rectCellsEquiv s (i, b))
  invFun f c := f ((rectCellsEquiv s).symm c).1 ((rectCellsEquiv s).symm c).2
  left_inv f := by
    funext c
    simp
  right_inv f := by
    funext i b
    simp

private def IsRectArray {s D : ℕ} (f : Fin s → Bool → Fin D) : Prop :=
  (∀ i, f i false ≤ f i true) ∧
    StrictMono (fun i => f i false) ∧ StrictMono (fun i => f i true)

private lemma semistandard_rect_iff_array {s D : ℕ} (f : (rect s).cells → Fin D) :
    IsSemistandard (rect s) f ↔ IsRectArray (rectFunctionEquiv s D f) := by
  constructor
  · rintro ⟨hrow, hcol⟩
    change (∀ i, f (rectCellsEquiv s (i, false)) ≤ f (rectCellsEquiv s (i, true))) ∧
      StrictMono (fun i => f (rectCellsEquiv s (i, false))) ∧
      StrictMono (fun i => f (rectCellsEquiv s (i, true)))
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact hrow (rectCellsEquiv s (i, false)) (rectCellsEquiv s (i, true)) rfl (by
        change 0 ≤ 1
        omega)
    · intro i j hij
      exact hcol (rectCellsEquiv s (i, false)) (rectCellsEquiv s (j, false)) rfl
        (Fin.lt_def.mp hij)
    · intro i j hij
      exact hcol (rectCellsEquiv s (i, true)) (rectCellsEquiv s (j, true)) rfl
        (Fin.lt_def.mp hij)
  · rintro ⟨hrow, hcol₀, hcol₁⟩
    constructor
    · intro a b hab hcol
      let x := (rectCellsEquiv s).symm a
      let y := (rectCellsEquiv s).symm b
      have hx := (rectCellsEquiv s).apply_symm_apply a
      have hy := (rectCellsEquiv s).apply_symm_apply b
      have hrow' : x.1 = y.1 := by
        apply Fin.ext
        have hx' := congrArg (fun z : {c // c ∈ rect s} => z.1.1) hx
        have hy' := congrArg (fun z : {c // c ∈ rect s} => z.1.1) hy
        simpa [x, y, rectCellsEquiv] using hx'.trans (hab.trans hy'.symm)
      have hxcol : (if x.2 then 1 else 0) = a.1.2 := by
        change (if decide (a.1.2 = 1) then 1 else 0) = a.1.2
        rcases (rectCellCoordinates s a).2 with h | h <;> simp [h]
      have hycol : (if y.2 then 1 else 0) = b.1.2 := by
        change (if decide (b.1.2 = 1) then 1 else 0) = b.1.2
        rcases (rectCellCoordinates s b).2 with h | h <;> simp [h]
      have hcol' : (if x.2 then 1 else 0) ≤ (if y.2 then 1 else 0) := by
        calc
          _ = a.1.2 := hxcol
          _ ≤ b.1.2 := hcol
          _ = _ := hycol.symm
      have hval : (rectFunctionEquiv s D f) x.1 x.2 ≤
          (rectFunctionEquiv s D f) y.1 y.2 := by
        rw [hrow']
        cases hxBool : x.2 <;> cases hyBool : y.2
        · exact le_rfl
        · simpa [rectFunctionEquiv] using hrow y.1
        · norm_num [hxBool, hyBool] at hcol'
        · exact le_rfl
      simpa [x, y, rectFunctionEquiv] using hval
    · intro a b hab hrow
      let x := (rectCellsEquiv s).symm a
      let y := (rectCellsEquiv s).symm b
      have hx := (rectCellsEquiv s).apply_symm_apply a
      have hy := (rectCellsEquiv s).apply_symm_apply b
      have hxrow : x.1.1 = a.1.1 := by
        dsimp [x, rectCellsEquiv]
      have hyrow : y.1.1 = b.1.1 := by
        dsimp [y, rectCellsEquiv]
      have hxcol : (if x.2 then 1 else 0) = a.1.2 := by
        change (if decide (a.1.2 = 1) then 1 else 0) = a.1.2
        rcases (rectCellCoordinates s a).2 with h | h <;> simp [h]
      have hycol : (if y.2 then 1 else 0) = b.1.2 := by
        change (if decide (b.1.2 = 1) then 1 else 0) = b.1.2
        rcases (rectCellCoordinates s b).2 with h | h <;> simp [h]
      have hcolEq : (if x.2 then 1 else 0) = (if y.2 then 1 else 0) :=
        hxcol.trans (hab.trans hycol.symm)
      have hcol' : x.2 = y.2 := by
        cases hxBool : x.2 <;> cases hyBool : y.2
        · rfl
        · norm_num [hxBool, hyBool] at hcolEq
        · norm_num [hxBool, hyBool] at hcolEq
        · rfl
      have hltNat : x.1.1 < y.1.1 := by
        calc
          x.1.1 = a.1.1 := hxrow
          _ < b.1.1 := hrow
          _ = y.1.1 := hyrow.symm
      have hlt : x.1 < y.1 := by
        exact Fin.lt_def.mpr hltNat
      have hval : (rectFunctionEquiv s D f) x.1 x.2 <
          (rectFunctionEquiv s D f) y.1 y.2 := by
        rw [← hcol']
        cases x.2
        · exact hcol₀ hlt
        · exact hcol₁ hlt
      simpa [x, y, rectFunctionEquiv] using hval

private lemma eval_esymm_one (D k : ℕ) :
    MvPolynomial.eval (fun _ : Fin D => (1 : ℤ)) (esymm (Fin D) ℤ k) =
      (D.choose k : ℤ) := by
  simp [MvPolynomial.esymm]

open Classical in
private lemma eval_schur_rect_one (D s : ℕ) :
    (Fintype.card {f : (rect s).cells → Fin D // IsSemistandard (rect s) f} : ℤ) =
      MvPolynomial.eval (fun _ : Fin D => (1 : ℤ)) (schur (rect s) D) := by
  classical
  simp [schur, MvPolynomial.eval, Fintype.card_subtype]

private def standardPairArrayEquiv (D s : ℕ) :
    {p : (Fin s ↪o Fin D) × (Fin s ↪o Fin D) // ∀ i, p.1 i ≤ p.2 i} ≃
      {IJ : PairIdx D s s // IsStandardPair IJ.1 IJ.2} where
  toFun p := ⟨(Set.powersetCard.ofFinEmbEquiv p.1.1,
      Set.powersetCard.ofFinEmbEquiv p.1.2), by
    intro i
    simpa only [subsetElem, ← Set.powersetCard.ofFinEmbEquiv_symm_apply,
      Equiv.symm_apply_apply] using p.2 i⟩
  invFun IJ := ⟨(Set.powersetCard.ofFinEmbEquiv.symm IJ.1.1,
      Set.powersetCard.ofFinEmbEquiv.symm IJ.1.2), by
    intro i
    simpa [subsetElem, Set.powersetCard.ofFinEmbEquiv_symm_apply] using IJ.2 i⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv IJ := by
    apply Subtype.ext
    simp

private def rectArrayPairEquiv (s D : ℕ) :
    {f : Fin s → Bool → Fin D // IsRectArray f} ≃
      {p : (Fin s ↪o Fin D) × (Fin s ↪o Fin D) // ∀ i, p.1 i ≤ p.2 i} where
  toFun f := ⟨(OrderEmbedding.ofStrictMono (fun i => f.1 i false) f.2.2.1,
      OrderEmbedding.ofStrictMono (fun i => f.1 i true) f.2.2.2), by
    intro i
    exact f.2.1 i⟩
  invFun p := ⟨fun i b => if b then p.1.2 i else p.1.1 i, by
    constructor
    · intro i
      simpa using p.2 i
    · constructor
      · intro i j hij
        simpa using p.1.1.strictMono hij
      · intro i j hij
        simpa using p.1.2.strictMono hij⟩
  left_inv f := by
    apply Subtype.ext
    funext i b
    cases b <;> rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      rfl
    · ext i
      rfl

private noncomputable def standardPairFillingEquiv (D s : ℕ) :
    {f : (rect s).cells → Fin D // IsSemistandard (rect s) f} ≃
      {IJ : PairIdx D s s // IsStandardPair IJ.1 IJ.2} := by
  let e₁ : {f : (rect s).cells → Fin D // IsSemistandard (rect s) f} ≃
      {f : Fin s → Bool → Fin D // IsRectArray f} :=
    (rectFunctionEquiv s D).subtypeEquiv fun f =>
      (semistandard_rect_iff_array (s := s) (D := D) f)
  exact e₁.trans ((rectArrayPairEquiv s D).trans (standardPairArrayEquiv D s))

open Classical in
/-- The number of standard pairs is `C(D,s)² - C(D,s+1) C(D,s-1)`. -/
theorem card_standardPairs (D s : ℕ) (hs : 1 ≤ s) :
    Fintype.card {IJ : PairIdx D s s // IsStandardPair IJ.1 IJ.2} =
      D.choose s ^ 2 - D.choose (s + 1) * D.choose (s - 1) := by
  classical
  let F := {f : (rect s).cells → Fin D // IsSemistandard (rect s) f}
  let N := Fintype.card F
  let A : ℕ := D.choose s ^ 2
  let B : ℕ := D.choose (s + 1) * D.choose (s - 1)
  have hcard : Fintype.card {IJ : PairIdx D s s // IsStandardPair IJ.1 IJ.2} = N := by
    exact Fintype.card_congr (standardPairFillingEquiv D s).symm
  have hSchur : (N : ℤ) =
      MvPolynomial.eval (fun _ : Fin D => (1 : ℤ)) (schur (rect s) D) := by
    exact eval_schur_rect_one D s
  have hJT : MvPolynomial.eval (fun _ : Fin D => (1 : ℤ)) (schur (rect s) D) =
      (D.choose s : ℤ) ^ 2 - (D.choose (s + 1) : ℤ) * (D.choose (s - 1) : ℤ) := by
    rw [show rect s = twoCol s s le_rfl by rfl,
      schur_twoCol D s s le_rfl hs]
    simp [eval_esymm_one]
    <;> ring
  have hInt : (N : ℤ) = (A : ℤ) - (B : ℤ) := by
    simpa [A, B] using hSchur.trans hJT
  have hBoundInt : (B : ℤ) ≤ (A : ℤ) := by
    have hnonneg : (0 : ℤ) ≤ (A : ℤ) - (B : ℤ) := by
      rw [← hInt]
      exact_mod_cast (Nat.zero_le N)
    omega
  have hBound : B ≤ A := by exact_mod_cast hBoundInt
  have hNat : (N : ℤ) = ((A - B : ℕ) : ℤ) := by
    rw [Nat.cast_sub hBound]
    exact hInt
  rw [hcard]
  exact_mod_cast hNat

/-- The products `det Y_I · det Y_J` over standard pairs are linearly independent. -/
theorem maxMinor_products_linearIndependent (D s : ℕ) :
    LinearIndependent ℂ
      (fun IJ : {IJ : PairIdx D s s // IsStandardPair IJ.1 IJ.2} =>
        maxMinor IJ.1.1 * maxMinor IJ.1.2) := by
  classical
  apply linearIndependent_of_distinct_degree (minorMonomialOrder D s)
    (fun IJ : {IJ : PairIdx D s s // IsStandardPair IJ.1 IJ.2} =>
      maxMinor IJ.1.1 * maxMinor IJ.1.2)
  · intro IJ IJ' h
    rw [maxMinor_product_degree, maxMinor_product_degree] at h
    obtain ⟨hI, hJ⟩ := standardPairExponent_injective IJ.2 IJ'.2 h
    exact Subtype.ext (Prod.ext hI hJ)
  · intro IJ
    exact maxMinor_product_leadingCoeff IJ.1.1 IJ.1.2

end Kraw
