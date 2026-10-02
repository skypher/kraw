import Kraw.GLRep
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace Kraw.GLSurjAux

open scoped Matrix

private abbrev PairIndex (D a b : ℕ) :=
  Set.powersetCard (Fin D) a × Set.powersetCard (Fin D) b

private def positionSign (R : Type*) [CommRing R] {D : ℕ}
    (A : Finset (Fin D)) (i : Fin D) : R :=
  (-1 : R) ^ (A.filter fun j => j < i).card

private lemma positionSign_erase {R : Type*} [CommRing R] {D : ℕ}
    (A : Finset (Fin D)) {i j : Fin D} (hi : i ∈ A) :
    positionSign R (A.erase i) j =
      if i < j then -positionSign R A j else positionSign R A j := by
  unfold positionSign
  rw [Finset.filter_erase]
  by_cases hij : i < j
  · have himem : i ∈ A.filter fun k => k < j := Finset.mem_filter.mpr ⟨hi, hij⟩
    rw [if_pos hij, Finset.card_erase_of_mem himem]
    let n := (A.filter fun k => k < j).card
    have hn : 1 ≤ n := Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨i, himem⟩)
    calc
      (-1 : R) ^ ((A.filter fun k => k < j).card - 1) =
          -((-1 : R) ^ (((A.filter fun k => k < j).card - 1) + 1)) := by
        rw [pow_succ]
        ring
      _ = -((-1 : R) ^ (A.filter fun k => k < j).card) := by
        rw [Nat.sub_add_cancel hn]
  · have himem : i ∉ A.filter fun k => k < j := by simp [hij]
    simp [hij, himem]

private lemma positionSign_insert {R : Type*} [CommRing R] {D : ℕ}
    (A : Finset (Fin D)) {i j : Fin D} (hi : i ∉ A) :
    positionSign R (insert i A) j =
      if i < j then -positionSign R A j else positionSign R A j := by
  unfold positionSign
  rw [Finset.filter_insert]
  by_cases hij : i < j
  · have himem : i ∉ A.filter fun k => k < j := by simp [hi, hij]
    rw [if_pos hij, if_pos hij, Finset.card_insert_of_notMem himem]
    rw [pow_succ]
    ring
  · simp [hij]

private lemma positionSign_erase_mul_insert {R : Type*} [CommRing R] {D : ℕ}
    (A B : Finset (Fin D)) {i j : Fin D} (hiA : i ∈ A) (hiB : i ∉ B) :
    positionSign R (A.erase i) j * positionSign R (insert i B) j =
      positionSign R A j * positionSign R B j := by
  rw [@positionSign_erase R _ D A i j hiA, @positionSign_insert R _ D B i j hiB]
  by_cases hij : i < j <;> simp [hij] <;> ring

private lemma positionSign_insert_mul_erase {R : Type*} [CommRing R] {D : ℕ}
    (A B : Finset (Fin D)) {i j : Fin D} (hiA : i ∉ A) (hiB : i ∈ B) :
    positionSign R (insert i A) j * positionSign R (B.erase i) j =
      positionSign R A j * positionSign R B j := by
  have h := positionSign_erase_mul_insert (R := R) B A hiB hiA (i := i) (j := j)
  calc
    _ = positionSign R (B.erase i) j * positionSign R (insert i A) j := by ring
    _ = positionSign R B j * positionSign R A j := h
    _ = _ := by ring

private lemma positionSign_erase_self {R : Type*} [CommRing R] {D : ℕ}
    (A : Finset (Fin D)) {i : Fin D} (hi : i ∈ A) :
    positionSign R (A.erase i) i = positionSign R A i := by
  rw [@positionSign_erase R _ D A i i hi]
  simp

private lemma positionSign_insert_self {R : Type*} [CommRing R] {D : ℕ}
    (A : Finset (Fin D)) {i : Fin D} (hi : i ∉ A) :
    positionSign R (insert i A) i = positionSign R A i := by
  rw [@positionSign_insert R _ D A i i hi]
  simp

private lemma positionSign_mul_self {R : Type*} [CommRing R] {D : ℕ}
    (A : Finset (Fin D)) (i : Fin D) :
    positionSign R A i * positionSign R A i = 1 := by
  change (-1 : R) ^ (A.filter fun j => j < i).card *
      (-1 : R) ^ (A.filter fun j => j < i).card = 1
  rw [← pow_add, ← Nat.two_mul, pow_mul]
  norm_num

private def forwardPair (D a b : ℕ) (P : PairIndex D a b) (i : Fin D)
    (hiA : i ∉ P.1.1) (hiB : i ∈ P.2.1) : PairIndex D (a + 1) (b - 1) :=
  (insertCoordinate P.1 i hiA, eraseCoordinate P.2 i hiB)

private def backwardPair (D a b : ℕ) (P : PairIndex D (a + 1) (b - 1)) (i : Fin D)
    (hiA : i ∈ P.1.1) (hiB : i ∉ P.2.1) (hb : 1 ≤ b) : PairIndex D a b :=
  (⟨P.1.1.erase i, by
      change (P.1.1.erase i).card = a
      rw [Finset.card_erase_of_mem hiA, P.1.2]
      omega⟩,
   ⟨insert i P.2.1, by
      change (insert i P.2.1).card = b
      rw [Finset.card_insert_of_notMem hiB, P.2.2]
      omega⟩)

private def upMove {R : Type*} [CommRing R] (D a b : ℕ) (i : Fin D) :
    (PairIndex D (a + 1) (b - 1) → R) →ₗ[R] (PairIndex D a b → R) where
  toFun f P :=
    if hiA : i ∉ P.1.1 then
      if hiB : i ∈ P.2.1 then
        positionSign R P.1.1 i * positionSign R P.2.1 i * f (forwardPair D a b P i hiA hiB)
      else 0
    else 0
  map_add' f g := by
    funext P
    by_cases hiA : i ∈ P.1.1
    · simp [hiA]
    · by_cases hiB : i ∈ P.2.1 <;> simp [hiA, hiB, mul_add]
  map_smul' c f := by
    funext P
    by_cases hiA : i ∈ P.1.1
    · simp [hiA]
    · by_cases hiB : i ∈ P.2.1 <;>
        simp [hiA, hiB, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

private def downMove {R : Type*} [CommRing R] (D a b : ℕ) (i : Fin D) :
    (PairIndex D a b → R) →ₗ[R] (PairIndex D (a + 1) (b - 1) → R) where
  toFun f P :=
    if hiA : i ∈ P.1.1 then
      if hiB : i ∉ P.2.1 then
        if hb : 1 ≤ b then
          positionSign R P.1.1 i * positionSign R P.2.1 i *
            f (backwardPair D a b P i hiA hiB hb)
        else 0
      else 0
    else 0
  map_add' f g := by
    funext P
    by_cases hiA : i ∈ P.1.1
    · by_cases hiB : i ∈ P.2.1
      · simp [hiA, hiB]
      · by_cases hb : 1 ≤ b <;> simp [hiA, hiB, hb, mul_add]
    · simp [hiA]
  map_smul' c f := by
    funext P
    by_cases hiA : i ∈ P.1.1
    · by_cases hiB : i ∈ P.2.1
      · simp [hiA, hiB]
      · by_cases hb : 1 ≤ b <;>
          simp [hiA, hiB, hb, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    · simp [hiA]

private lemma down_up_same {R : Type*} [CommRing R] (D a b : ℕ) (i : Fin D)
    (hb : 1 ≤ b) (f : PairIndex D (a + 1) (b - 1) → R)
    (P : PairIndex D (a + 1) (b - 1)) :
    ((downMove (R := R) D a b i).comp (upMove (R := R) D a b i)) f P =
      if i ∈ P.1.1 ∧ i ∉ P.2.1 then f P else 0 := by
  classical
  by_cases hiA : i ∈ P.1.1
  · by_cases hiB : i ∈ P.2.1
    · simp [downMove, upMove, hiA, hiB]
    · have hcoeff :
          (positionSign R P.1.1 i * positionSign R P.2.1 i) *
              (positionSign R P.1.1 i * positionSign R P.2.1 i) = 1 := by
        have hA := positionSign_mul_self (R := R) P.1.1 i
        have hB := positionSign_mul_self (R := R) P.2.1 i
        calc
          _ = (positionSign R P.1.1 i * positionSign R P.1.1 i) *
              (positionSign R P.2.1 i * positionSign R P.2.1 i) := by ring
          _ = 1 := by rw [hA, hB]; ring
      simp [downMove, upMove, hiA, hiB, hb, backwardPair, forwardPair,
        insertCoordinate, eraseCoordinate, positionSign_erase_self,
        positionSign_insert_self, hcoeff]
      calc
        _ = (positionSign R P.1.1 i * positionSign R P.2.1 i *
            (positionSign R P.1.1 i * positionSign R P.2.1 i)) * f P := by ring
        _ = f P := by rw [hcoeff]; simp
  · simp [downMove, upMove, hiA]

private lemma up_down_same {R : Type*} [CommRing R] (D a b : ℕ) (i : Fin D)
    (f : PairIndex D (a + 1) (b - 1) → R)
    (P : PairIndex D (a + 1) (b - 1)) :
    ((upMove (R := R) D (a + 1) (b - 1) i).comp
      (downMove (R := R) D (a + 1) (b - 1) i)) f P =
      if i ∉ P.1.1 ∧ i ∈ P.2.1 then f P else 0 := by
  classical
  by_cases hiA : i ∈ P.1.1
  · simp [upMove, hiA]
  · by_cases hiB : i ∈ P.2.1
    · have hb : 1 ≤ b - 1 := by
        have hcard := P.2.2
        change (P.2.1).card = b - 1 at hcard
        have hpos : 0 < (P.2.1).card := Finset.card_pos.mpr ⟨i, hiB⟩
        omega
      have hcoeff :
          (positionSign R P.1.1 i * positionSign R P.2.1 i) *
              (positionSign R P.1.1 i * positionSign R P.2.1 i) = 1 := by
        have hA := positionSign_mul_self (R := R) P.1.1 i
        have hB := positionSign_mul_self (R := R) P.2.1 i
        calc
          _ = (positionSign R P.1.1 i * positionSign R P.1.1 i) *
              (positionSign R P.2.1 i * positionSign R P.2.1 i) := by ring
          _ = 1 := by rw [hA, hB]; ring
      simp [upMove, downMove, hiA, hiB, hb, backwardPair, forwardPair,
        insertCoordinate, eraseCoordinate, positionSign_erase_self,
        positionSign_insert_self, hcoeff]
      calc
        _ = (positionSign R P.1.1 i * positionSign R P.2.1 i *
            (positionSign R P.1.1 i * positionSign R P.2.1 i)) * f P := by ring
        _ = f P := by rw [hcoeff]; simp
    · simp [upMove, hiA, hiB]

private lemma down_up_offdiag_ge2 {R : Type*} [CommRing R] (D a b : ℕ) (i j : Fin D)
    (hbb : 2 ≤ b) (hij : i ≠ j)
    (f : PairIndex D (a + 1) (b - 1) → R) (P : PairIndex D (a + 1) (b - 1)) :
    ((downMove (R := R) D a b i).comp (upMove (R := R) D a b j)) f P =
      ((upMove (R := R) D (a + 1) (b - 1) j).comp
        (downMove (R := R) D (a + 1) (b - 1) i)) f P := by
  classical
  have hb : 1 ≤ b := by omega
  have hb' : 1 ≤ b - 1 := by omega
  have hAset : insert j (P.1.1.erase i) = (insert j P.1.1).erase i :=
    (Finset.erase_insert_of_ne (Ne.symm hij)).symm
  have hBset : (insert i P.2.1).erase j = insert i (P.2.1.erase j) :=
    Finset.erase_insert_of_ne hij
  by_cases hiA : i ∈ P.1.1 <;>
    by_cases hiB : i ∈ P.2.1 <;>
    by_cases hjA : j ∈ P.1.1 <;>
    by_cases hjB : j ∈ P.2.1
  all_goals
    simp [LinearMap.comp_apply, downMove, upMove, hiA, hiB, hjA, hjB,
      hb, hb', hij, Ne.symm hij, backwardPair, forwardPair,
      insertCoordinate, eraseCoordinate, positionSign_erase_mul_insert,
      positionSign_insert_mul_erase, hAset, hBset] <;> ring

private lemma down_up_offdiag {R : Type*} [CommRing R] (D a b : ℕ) (i j : Fin D)
    (hb : 1 ≤ b) (hij : i ≠ j)
    (f : PairIndex D (a + 1) (b - 1) → R) (P : PairIndex D (a + 1) (b - 1)) :
    ((downMove (R := R) D a b i).comp (upMove (R := R) D a b j)) f P =
      ((upMove (R := R) D (a + 1) (b - 1) j).comp
        (downMove (R := R) D (a + 1) (b - 1) i)) f P := by
  by_cases hbb : 2 ≤ b
  · exact down_up_offdiag_ge2 D a b i j hbb hij f P
  · have hbEq : b = 1 := by omega
    subst b
    have hP2 : P.2.1 = ∅ := Finset.card_eq_zero.mp (by simpa using P.2.2)
    by_cases hiA : i ∈ P.1.1
    · simp [LinearMap.comp_apply, downMove, upMove, hiA, hP2, hij, Ne.symm hij,
        backwardPair, forwardPair, insertCoordinate, eraseCoordinate]
    · simp [LinearMap.comp_apply, downMove, upMove, hiA, hP2, hij, Ne.symm hij]

def sumUp {R : Type*} [CommRing R] (D a b : ℕ) :
    (PairIndex D (a + 1) (b - 1) → R) →ₗ[R] (PairIndex D a b → R) :=
  ∑ i : Fin D, upMove (R := R) D a b i

def sumDown {R : Type*} [CommRing R] (D a b : ℕ) :
    (PairIndex D a b → R) →ₗ[R] (PairIndex D (a + 1) (b - 1) → R) :=
  ∑ i : Fin D, downMove (R := R) D a b i

private lemma sum_indicator {R : Type*} [AddCommMonoid R] (D : ℕ)
    (S : Finset (Fin D)) (x : R) :
    (∑ i : Fin D, if i ∈ S then x else 0) = (S.card : ℕ) • x := by
  classical
  rw [Finset.sum_ite_mem_eq]
  simp

private lemma pair_commutator_sum {R : Type*} [CommRing R] (D s : ℕ)
    (hs : 1 ≤ s) (i : Fin D)
    (f : PairIndex D (s + 1) (s - 1) → R)
    (P : PairIndex D (s + 1) (s - 1)) :
    (∑ j : Fin D, ((downMove (R := R) D s s i).comp
      (upMove (R := R) D s s j)) f P) -
    (∑ j : Fin D, ((upMove (R := R) D (s + 1) (s - 1) j).comp
      (downMove (R := R) D (s + 1) (s - 1) i)) f P) =
      (if i ∈ P.1.1 \ P.2.1 then f P else 0) -
      (if i ∈ P.2.1 \ P.1.1 then f P else 0) := by
  classical
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · rw [down_up_same D s s i hs f P, up_down_same D s s i f P]
    simp [Finset.mem_sdiff, and_comm]
  · intro j _ hji
    rw [down_up_offdiag D s s i j hs (Ne.symm hji) f P]
    simp
  · simp

private lemma subset_card_difference {D s : ℕ} (P : PairIndex D (s + 1) (s - 1))
    (hs : 1 ≤ s) :
    (P.1.1 \ P.2.1).card = (P.2.1 \ P.1.1).card + 2 := by
  have hcardA : P.1.1.card = s + 1 := P.1.2
  have hcardB : P.2.1.card = s - 1 := P.2.2
  have hA := Finset.card_sdiff_add_card_inter P.1.1 P.2.1
  have hB := Finset.card_sdiff_add_card_inter P.2.1 P.1.1
  rw [hcardA] at hA
  rw [hcardB] at hB
  rw [Finset.inter_comm] at hB
  omega

noncomputable def transferCoord (D s : ℕ) :
    (PairIndex D s s → ℂ) →ₗ[ℂ] (PairIndex D (s + 1) (s - 1) → ℂ) :=
  (coordinateTensorBasis D (s + 1) (s - 1)).equivFun.toLinearMap ∘ₗ
    transferMap D s ∘ₗ (coordinateTensorBasis D s s).equivFun.symm.toLinearMap

private lemma backward_forward {D s : ℕ}
    (Q : PairIndex D (s + 1) (s - 1)) (i : Fin D)
    (hiA : i ∈ Q.1.1) (hiB : i ∉ Q.2.1) (hs : 1 ≤ s) :
    forwardPair D s s (backwardPair D s s Q i hiA hiB hs) i
      (by simp [backwardPair]) (by simp [backwardPair]) = Q := by
  apply Prod.ext
  · apply Subtype.ext
    simp [forwardPair, backwardPair, insertCoordinate, eraseCoordinate,
      Finset.insert_erase hiA]
  · apply Subtype.ext
    simp [forwardPair, backwardPair, insertCoordinate, eraseCoordinate,
      Finset.erase_insert hiB]

private lemma forward_backward {D s : ℕ}
    (P : PairIndex D s s) (i : Fin D)
    (hiA : i ∉ P.1.1) (hiB : i ∈ P.2.1) (hs : 1 ≤ s) :
    backwardPair D s s (forwardPair D s s P i hiA hiB) i
      (by simp [forwardPair, insertCoordinate, eraseCoordinate])
      (by simp [forwardPair, insertCoordinate, eraseCoordinate]) hs = P := by
  apply Prod.ext
  · apply Subtype.ext
    simp [forwardPair, backwardPair, insertCoordinate, eraseCoordinate,
      Finset.erase_insert hiA]
  · apply Subtype.ext
    simp [forwardPair, backwardPair, insertCoordinate, eraseCoordinate,
      Finset.insert_erase hiB]

private lemma backward_eq_implies_not_mem_first {D s : ℕ}
    (Q : PairIndex D (s + 1) (s - 1)) (i : Fin D)
    (hiA : i ∈ Q.1.1) (hiB : i ∉ Q.2.1) (hs : 1 ≤ s)
    (P : PairIndex D s s)
    (h : backwardPair D s s Q i hiA hiB hs = P) : i ∉ P.1.1 := by
  intro hP
  have hback : i ∈ (backwardPair D s s Q i hiA hiB hs).1.1 := by
    simpa [h] using hP
  simpa [backwardPair] using hback

private lemma backward_eq_implies_mem_second {D s : ℕ}
    (Q : PairIndex D (s + 1) (s - 1)) (i : Fin D)
    (hiA : i ∈ Q.1.1) (hiB : i ∉ Q.2.1) (hs : 1 ≤ s)
    (P : PairIndex D s s)
    (h : backwardPair D s s Q i hiA hiB hs = P) : i ∈ P.2.1 := by
  have hback : i ∈ (backwardPair D s s Q i hiA hiB hs).2.1 := by simp [backwardPair]
  simpa [h] using hback

private lemma forward_eq_iff_backward_eq {D s : ℕ}
    (P : PairIndex D s s) (Q : PairIndex D (s + 1) (s - 1)) (i : Fin D)
    (hiA : i ∉ P.1.1) (hiB : i ∈ P.2.1)
    (hqA : i ∈ Q.1.1) (hqB : i ∉ Q.2.1) (hs : 1 ≤ s) :
    forwardPair D s s P i hiA hiB = Q ↔
      backwardPair D s s Q i hqA hqB hs = P := by
  constructor
  · intro h
    subst Q
    exact forward_backward P i hiA hiB hs
  · intro h
    subst P
    exact backward_forward Q i hqA hqB hs

private lemma coordinateTensorBasis_equivFun_apply {D k l : ℕ}
    (P Q : PairIndex D k l) :
    (coordinateTensorBasis D k l).equivFun
        (coordinateTensorBasis D k l P) Q = if P = Q then 1 else 0 := by
  simp [Module.Basis.equivFun_self]

theorem transferCoord_eq_sumDown (D s : ℕ) (hs : 1 ≤ s) :
    transferCoord D s = sumDown (R := ℂ) D s s := by
  classical
  apply (Pi.basisFun ℂ (PairIndex D s s)).ext
  intro P
  funext Q
  have hsource :
      (coordinateTensorBasis D s s).equivFun.symm (Pi.single P 1) =
        coordinateTensorBasis D s s P := by
    apply (coordinateTensorBasis D s s).equivFun.injective
    funext Q'
    simp [Module.Basis.equivFun_self]
  simp only [transferCoord, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Pi.basisFun_apply, hsource]
  change ((coordinateTensorBasis D (s + 1) (s - 1)).equivFun.toLinearMap
      (transferMap D s (coordinateTensorBasis D s s P))) Q =
    (sumDown (R := ℂ) D s s (Pi.single P 1)) Q
  rw [transferMap, Module.Basis.constr_basis]
  rw [map_sum, sumDown, LinearMap.sum_apply]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hA : c ∈ P.1.1
  · have hnotA : ¬ c ∉ P.1.1 := by simpa using hA
    rw [dif_neg hnotA]
    simp only [map_zero, Pi.zero_apply]
    by_cases hQA : c ∈ Q.1.1
    · by_cases hQB : c ∈ Q.2.1
      · simp [downMove, hQA, hQB]
      · have hne := backward_eq_implies_not_mem_first Q c hQA hQB hs P
        have hneq : backwardPair D s s Q c hQA hQB hs ≠ P := by
          intro heq
          exact hne heq hA
        simp [downMove, hQA, hQB, hs, Pi.single_apply, hneq]
    · simp [downMove, hQA]
  · by_cases hB : c ∈ P.2.1
    · have hposA : c ∉ P.1.1 := hA
      have hvec :
          (coordinateWedgeBasis D (s + 1) (insertCoordinate P.1 c hposA) ⊗ₜ[ℂ]
            coordinateWedgeBasis D (s - 1) (eraseCoordinate P.2 c hB)) =
          coordinateTensorBasis D (s + 1) (s - 1)
            (forwardPair D s s P c hposA hB) := by
        simp [coordinateTensorBasis, forwardPair, Module.Basis.tensorProduct_apply]
      rw [dif_pos hposA, dif_pos hB, map_smul, hvec]
      change (wedgePositionSign P.1.1 c * wedgePositionSign P.2.1 c) *
          ((coordinateTensorBasis D (s + 1) (s - 1)).equivFun
            (coordinateTensorBasis D (s + 1) (s - 1)
              (forwardPair D s s P c hposA hB)) Q) =
        (downMove D s s c) (Pi.single P 1) Q
      rw [coordinateTensorBasis_equivFun_apply]
      by_cases hQA : c ∈ Q.1.1
      · by_cases hQB : c ∈ Q.2.1
        · have hne : forwardPair D s s P c hposA hB ≠ Q := by
            intro heq
            have hmem := hQB
            rw [← heq] at hmem
            simp [forwardPair, eraseCoordinate] at hmem
          simp [downMove, hQA, hQB, hne]
        · have hiff := forward_eq_iff_backward_eq P Q c hposA hB hQA hQB hs
          by_cases heq : forwardPair D s s P c hposA hB = Q
          · have hback := hiff.mp heq
            subst Q
            have hsign :
                wedgePositionSign P.1.1 c * wedgePositionSign P.2.1 c =
                  wedgePositionSign (insert c P.1.1) c *
                    wedgePositionSign (P.2.1.erase c) c := by
              change positionSign ℂ P.1.1 c * positionSign ℂ P.2.1 c =
                positionSign ℂ (insert c P.1.1) c *
                  positionSign ℂ (P.2.1.erase c) c
              rw [positionSign_insert_self (R := ℂ) P.1.1 hposA,
                positionSign_erase_self (R := ℂ) P.2.1 hB]
            simp
            have hback' := hback
            simp [forwardPair, insertCoordinate, eraseCoordinate] at hback'
            simpa [downMove, hQA, hQB, hs, hback, Pi.single_apply,
              hback', wedgePositionSign, positionSign, forwardPair, insertCoordinate,
              eraseCoordinate] using hsign
          · have hback :
                backwardPair D s s Q c hQA hQB hs ≠ P := by
              intro hb
              exact heq (hiff.mpr hb)
            simp [downMove, hQA, hQB, heq, hback]
      · have hne : forwardPair D s s P c hposA hB ≠ Q := by
          intro heq
          have hmem := hQA
          rw [← heq] at hmem
          simp [forwardPair, insertCoordinate] at hmem
        simp [downMove, hQA, hne]
    · have hnotB : ¬ c ∈ P.2.1 := by simpa using hB
      rw [dif_pos hA, dif_neg hnotB]
      simp only [map_zero, Pi.zero_apply]
      by_cases hQA : c ∈ Q.1.1
      · by_cases hQB : c ∈ Q.2.1
        · simp [downMove, hQA, hQB]
        · have hne := backward_eq_implies_mem_second Q c hQA hQB hs P
          have hneq : backwardPair D s s Q c hQA hQB hs ≠ P := by
            intro heq
            exact hnotB (hne heq)
          simp [downMove, hQA, hQB, hs, Pi.single_apply, hneq]
      · simp [downMove, hQA]

theorem coordinate_commutator {R : Type*} [CommRing R] (D s : ℕ)
    (hs : 1 ≤ s) :
    (sumDown (R := R) D s s).comp (sumUp (R := R) D s s) -
    (sumUp (R := R) D (s + 1) (s - 1)).comp
        (sumDown (R := R) D (s + 1) (s - 1)) =
      (2 : R) • LinearMap.id := by
  classical
  apply LinearMap.ext
  intro f
  funext P
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, sumDown, sumUp,
    LinearMap.sum_apply, map_sum, Pi.sub_apply, Finset.sum_apply]
  change (∑ x : Fin D, ∑ d : Fin D,
      (downMove (R := R) D s s d) ((upMove (R := R) D s s x) f) P) -
    (∑ x : Fin D, ∑ d : Fin D,
      (upMove (R := R) D (s + 1) (s - 1) d)
        ((downMove (R := R) D (s + 1) (s - 1) x) f) P) = (2 : R) • f P
  calc
    _ = (∑ d : Fin D, ∑ x : Fin D,
          (downMove (R := R) D s s d) ((upMove (R := R) D s s x) f) P) -
        (∑ d : Fin D, ∑ x : Fin D,
          (upMove (R := R) D (s + 1) (s - 1) x)
            ((downMove (R := R) D (s + 1) (s - 1) d) f) P) := by
      congr 1 <;> exact Finset.sum_comm
    _ = ∑ d : Fin D,
          ((∑ x : Fin D,
              (downMove (R := R) D s s d) ((upMove (R := R) D s s x) f) P) -
            (∑ x : Fin D,
              (upMove (R := R) D (s + 1) (s - 1) x)
                ((downMove (R := R) D (s + 1) (s - 1) d) f) P)) := by
      rw [← Finset.sum_sub_distrib]
    _ = ∑ d : Fin D,
          ((if d ∈ P.1.1 \ P.2.1 then f P else 0) -
            (if d ∈ P.2.1 \ P.1.1 then f P else 0)) := by
      congr 1
      funext d
      exact pair_commutator_sum D s hs d f P
    _ = (∑ d : Fin D, if d ∈ P.1.1 \ P.2.1 then f P else 0) -
        (∑ d : Fin D, if d ∈ P.2.1 \ P.1.1 then f P else 0) := by
      rw [Finset.sum_sub_distrib]
    _ = (P.1.1 \ P.2.1).card • f P - (P.2.1 \ P.1.1).card • f P := by
      rw [sum_indicator D (P.1.1 \ P.2.1) (f P),
        sum_indicator D (P.2.1 \ P.1.1) (f P)]
    _ = (2 : R) • f P := by
      rw [subset_card_difference P hs, add_nsmul]
      have hcast : (2 : R) • f P = (2 : ℕ) • f P :=
        Nat.cast_smul_eq_nsmul R 2 (f P)
      rw [hcast]
      exact add_sub_cancel_left
        ((P.2.1 \ P.1.1).card • f P) (2 • f P)

noncomputable def downMatrix {R : Type*} [CommRing R] (D a b : ℕ) :
    Matrix (PairIndex D (a + 1) (b - 1)) (PairIndex D a b) R :=
  LinearMap.toMatrix' (sumDown (R := R) D a b)

noncomputable def upMatrix {R : Type*} [CommRing R] (D a b : ℕ) :
    Matrix (PairIndex D a b) (PairIndex D (a + 1) (b - 1)) R :=
  LinearMap.toMatrix' (sumUp (R := R) D a b)

private lemma backward_forward_gen {D a b : ℕ}
    (Q : PairIndex D (a + 1) (b - 1)) (i : Fin D)
    (hiA : i ∈ Q.1.1) (hiB : i ∉ Q.2.1) (hb : 1 ≤ b) :
    forwardPair D a b (backwardPair D a b Q i hiA hiB hb) i
      (by simp [backwardPair]) (by simp [backwardPair]) = Q := by
  apply Prod.ext
  · apply Subtype.ext
    simp [forwardPair, backwardPair, insertCoordinate, eraseCoordinate,
      Finset.insert_erase hiA]
  · apply Subtype.ext
    simp [forwardPair, backwardPair, insertCoordinate, eraseCoordinate,
      Finset.erase_insert hiB]

private lemma forward_backward_gen {D a b : ℕ}
    (P : PairIndex D a b) (i : Fin D)
    (hiA : i ∉ P.1.1) (hiB : i ∈ P.2.1) (hb : 1 ≤ b) :
    backwardPair D a b (forwardPair D a b P i hiA hiB) i
      (by simp [forwardPair, insertCoordinate, eraseCoordinate])
      (by simp [forwardPair, insertCoordinate, eraseCoordinate]) hb = P := by
  apply Prod.ext
  · apply Subtype.ext
    simp [forwardPair, backwardPair, insertCoordinate, eraseCoordinate,
      Finset.erase_insert hiA]
  · apply Subtype.ext
    simp [forwardPair, backwardPair, insertCoordinate, eraseCoordinate,
      Finset.insert_erase hiB]

private lemma forward_eq_iff_backward_eq_gen {D a b : ℕ}
    (P : PairIndex D a b) (Q : PairIndex D (a + 1) (b - 1)) (i : Fin D)
    (hiA : i ∉ P.1.1) (hiB : i ∈ P.2.1)
    (hqA : i ∈ Q.1.1) (hqB : i ∉ Q.2.1) (hb : 1 ≤ b) :
    forwardPair D a b P i hiA hiB = Q ↔
      backwardPair D a b Q i hqA hqB hb = P := by
  constructor
  · intro h
    subst Q
    exact forward_backward_gen P i hiA hiB hb
  · intro h
    subst P
    exact backward_forward_gen Q i hqA hqB hb

private lemma forward_sign_eq_gen {R : Type*} [CommRing R] {D a b : ℕ}
    (P : PairIndex D a b) (Q : PairIndex D (a + 1) (b - 1)) (i : Fin D)
    (hiA : i ∉ P.1.1) (hiB : i ∈ P.2.1)
    (heq : forwardPair D a b P i hiA hiB = Q) :
    positionSign R Q.1.1 i * positionSign R Q.2.1 i =
      positionSign R P.1.1 i * positionSign R P.2.1 i := by
  have hfirst : Q.1.1 = insert i P.1.1 := by
    have hh := congrArg (fun X : PairIndex D (a + 1) (b - 1) => X.1.1) heq
    simpa [forwardPair, insertCoordinate] using hh.symm
  have hsecond : Q.2.1 = P.2.1.erase i := by
    have hh := congrArg (fun X : PairIndex D (a + 1) (b - 1) => X.2.1) heq
    simpa [forwardPair, eraseCoordinate] using hh.symm
  rw [hfirst, hsecond, positionSign_insert_self (R := R) P.1.1 hiA,
    positionSign_erase_self (R := R) P.2.1 hiB]

private lemma down_up_entry_eq {R : Type*} [CommRing R] {D a b : ℕ}
    (P : PairIndex D a b) (Q : PairIndex D (a + 1) (b - 1)) (i : Fin D) :
    (downMove (R := R) D a b i (Pi.single P 1)) Q =
      (upMove (R := R) D a b i (Pi.single Q 1)) P := by
  classical
  by_cases hqA : i ∈ Q.1.1
  · by_cases hqB : i ∈ Q.2.1
    · by_cases hpA : i ∈ P.1.1
      · simp [downMove, upMove, hqA, hqB, hpA]
      · by_cases hpB : i ∈ P.2.1
        · have hne : forwardPair D a b P i hpA hpB ≠ Q := by
            intro heq
            have hh := congrArg (fun X : PairIndex D (a + 1) (b - 1) => X.2.1) heq
            have hnot : i ∉ Q.2.1 := by
              rw [← hh]
              simp [forwardPair, eraseCoordinate]
            exact hnot hqB
          have hne' : (insertCoordinate P.1 i hpA, eraseCoordinate P.2 i hpB) ≠ Q := by
            simpa [forwardPair] using hne
          simp [downMove, upMove, hqA, hqB, hpA, hpB, hne',
            backwardPair, forwardPair, Pi.single_apply]
        · simp [downMove, upMove, hqA, hqB, hpA, hpB, backwardPair,
            forwardPair, Pi.single_apply]
    · by_cases hb : 1 ≤ b
      · by_cases hpA : i ∈ P.1.1
        · have hne : backwardPair D a b Q i hqA hqB hb ≠ P := by
            intro heq
            have hnot : i ∉ (backwardPair D a b Q i hqA hqB hb).1.1 := by
              simp [backwardPair]
            rw [heq] at hnot
            exact hnot hpA
          have hne' :
              ((⟨Q.1.1.erase i, by
                change (Q.1.1.erase i).card = a
                rw [Finset.card_erase_of_mem hqA, Q.1.2]
                omega⟩,
                ⟨insert i Q.2.1, by
                  change (insert i Q.2.1).card = b
                  rw [Finset.card_insert_of_notMem hqB, Q.2.2]
                  omega⟩) : PairIndex D a b) ≠ P := by
            simpa [backwardPair] using hne
          simp [downMove, upMove, hqA, hqB, hb, hpA, hne',
            backwardPair, forwardPair, Pi.single_apply]
        · by_cases hpB : i ∈ P.2.1
          · have hiff := forward_eq_iff_backward_eq_gen P Q i hpA hpB hqA hqB hb
            by_cases heq : forwardPair D a b P i hpA hpB = Q
            · have hback : backwardPair D a b Q i hqA hqB hb = P := hiff.mp heq
              have hsign := forward_sign_eq_gen (R := R) P Q i hpA hpB heq
              have heq' : (insertCoordinate P.1 i hpA, eraseCoordinate P.2 i hpB) = Q := by
                simpa [forwardPair] using heq
              have hback' :
                  ((⟨Q.1.1.erase i, by
                    change (Q.1.1.erase i).card = a
                    rw [Finset.card_erase_of_mem hqA, Q.1.2]
                    omega⟩,
                    ⟨insert i Q.2.1, by
                      change (insert i Q.2.1).card = b
                      rw [Finset.card_insert_of_notMem hqB, Q.2.2]
                      omega⟩) : PairIndex D a b) = P := by
                simpa [backwardPair] using hback
              simp [downMove, upMove, hqA, hqB, hb, hpA, hpB, hback, heq,
                hback', heq', hsign, backwardPair, forwardPair, Pi.single_apply]
            · have hback : backwardPair D a b Q i hqA hqB hb ≠ P := by
                intro hh
                exact heq (hiff.mpr hh)
              have hback' :
                  ((⟨Q.1.1.erase i, by
                    change (Q.1.1.erase i).card = a
                    rw [Finset.card_erase_of_mem hqA, Q.1.2]
                    omega⟩,
                    ⟨insert i Q.2.1, by
                      change (insert i Q.2.1).card = b
                      rw [Finset.card_insert_of_notMem hqB, Q.2.2]
                      omega⟩) : PairIndex D a b) ≠ P := by
                simpa [backwardPair] using hback
              have heq' : (insertCoordinate P.1 i hpA, eraseCoordinate P.2 i hpB) ≠ Q := by
                simpa [forwardPair] using heq
              simp [downMove, upMove, hqA, hqB, hb, hpA, hpB, hback', heq',
                backwardPair, forwardPair, Pi.single_apply]
          · have hback : backwardPair D a b Q i hqA hqB hb ≠ P := by
              intro heq
              have hmem : i ∈ (backwardPair D a b Q i hqA hqB hb).2.1 := by
                simp [backwardPair]
              rw [heq] at hmem
              exact hpB hmem
            simp [downMove, upMove, hqA, hqB, hb, hpA, hpB, hback,
              Pi.single_apply]
      · have hb0 : b = 0 := by omega
        have hcard : P.2.1.card = b := P.2.2
        have hP0 : P.2.1 = ∅ := Finset.card_eq_zero.mp (by omega)
        simp [downMove, upMove, hqA, hqB, hb, hP0]
  · by_cases hpA : i ∈ P.1.1
    · simp [downMove, upMove, hqA, hpA]
    · by_cases hpB : i ∈ P.2.1
      · have hne : forwardPair D a b P i hpA hpB ≠ Q := by
          intro heq
          have hh := congrArg (fun X : PairIndex D (a + 1) (b - 1) => X.1.1) heq
          have hmem : i ∈ Q.1.1 := by
            rw [← hh]
            simp [forwardPair, insertCoordinate]
          exact hqA hmem
        have hne' : (insertCoordinate P.1 i hpA, eraseCoordinate P.2 i hpB) ≠ Q := by
          simpa [forwardPair] using hne
        simp [downMove, upMove, hqA, hpA, hpB, hne',
          backwardPair, forwardPair, Pi.single_apply]
      · simp [downMove, upMove, hqA, hpA, hpB, backwardPair,
          forwardPair, Pi.single_apply]

private lemma upMatrix_eq_transpose_downMatrix (D a b : ℕ) :
    upMatrix (R := ℝ) D a b = (downMatrix (R := ℝ) D a b)ᵀ := by
  classical
  ext P Q
  change (sumUp (R := ℝ) D a b (Pi.single Q 1)) P =
    (sumDown (R := ℝ) D a b (Pi.single P 1)) Q
  simp only [sumUp, sumDown, LinearMap.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => (down_up_entry_eq (R := ℝ) P Q i).symm

private theorem gramPlusPosDef {ι κ μ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
    (A : Matrix ι κ ℝ) (B : Matrix μ ι ℝ)
    (hcomm : A * Aᵀ - Bᵀ * B = (2 : ℝ) • (1 : Matrix ι ι ℝ)) :
    (A * Aᵀ).PosDef := by
  have hBpos : (Bᵀ * B).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self B
  have htwo : ((2 : ℝ) • (1 : Matrix ι ι ℝ)).PosDef := by
    exact Matrix.PosDef.smul Matrix.PosDef.one (by norm_num)
  have hsum : A * Aᵀ = (2 : ℝ) • (1 : Matrix ι ι ℝ) + Bᵀ * B := by
    have h := congrArg (fun X : Matrix ι ι ℝ => X + Bᵀ * B) hcomm
    simpa [sub_add_cancel] using h
  rw [hsum]
  exact htwo.add_posSemidef hBpos

private theorem matrix_commutator (D s : ℕ) (hs : 1 ≤ s) :
    downMatrix (R := ℝ) D s s * (downMatrix (R := ℝ) D s s)ᵀ -
      (downMatrix (R := ℝ) D (s + 1) (s - 1))ᵀ *
        downMatrix (R := ℝ) D (s + 1) (s - 1) =
      (2 : ℝ) • (1 : Matrix (PairIndex D (s + 1) (s - 1))
        (PairIndex D (s + 1) (s - 1)) ℝ) := by
  classical
  have h := coordinate_commutator (R := ℝ) D s hs
  have hm := congrArg (fun f : _ →ₗ[ℝ] _ => LinearMap.toMatrix' f) h
  have hu₁ : LinearMap.toMatrix' (sumUp (R := ℝ) D s s) =
      (downMatrix (R := ℝ) D s s)ᵀ := by
    simpa [upMatrix, downMatrix] using upMatrix_eq_transpose_downMatrix D s s
  have hu₂ : LinearMap.toMatrix' (sumUp (R := ℝ) D (s + 1) (s - 1)) =
      (downMatrix (R := ℝ) D (s + 1) (s - 1))ᵀ := by
    simpa [upMatrix, downMatrix] using upMatrix_eq_transpose_downMatrix D (s + 1) (s - 1)
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, map_sub,
    map_smul, hu₁, hu₂, downMatrix, Nat.cast_ofNat] using hm

private theorem sumDown_surjective_real (D s : ℕ) (hs : 1 ≤ s) :
    Function.Surjective (sumDown (R := ℝ) D s s) := by
  classical
  let f := sumDown (R := ℝ) D s s
  let g := sumUp (R := ℝ) D s s
  have hpos := gramPlusPosDef (downMatrix (R := ℝ) D s s)
    (downMatrix (R := ℝ) D (s + 1) (s - 1)) (matrix_commutator D s hs)
  have hunitMatrix : IsUnit
      (LinearMap.toMatrix' (f.comp g)) := by
    have hunit := hpos.isUnit
    rw [LinearMap.toMatrix'_comp]
    change IsUnit (downMatrix (R := ℝ) D s s * upMatrix (R := ℝ) D s s)
    rw [upMatrix_eq_transpose_downMatrix]
    exact hunit
  have hunit : IsUnit (f.comp g) :=
    (LinearMap.isUnit_toMatrix'_iff).mp hunitMatrix
  have hrange : LinearMap.range (f.comp g) = ⊤ :=
    (LinearMap.isUnit_iff_range_eq_top (f.comp g)).mp hunit
  intro y
  have hy : y ∈ LinearMap.range (f.comp g) := by rw [hrange]; simp
  rcases hy with ⟨x, hx⟩
  exact ⟨g x, hx⟩

private lemma sumDown_complex_ofReal (D s : ℕ)
    (f : PairIndex D s s → ℝ) :
    sumDown (R := ℂ) D s s (fun P => (f P : ℂ)) =
      fun Q => ((sumDown (R := ℝ) D s s f Q : ℝ) : ℂ) := by
  classical
  funext Q
  simp only [sumDown, LinearMap.sum_apply, Finset.sum_apply]
  change (∑ i : Fin D,
      (downMove (R := ℂ) D s s i (fun P => (f P : ℂ))) Q) =
    algebraMap ℝ ℂ (∑ i : Fin D, (downMove (R := ℝ) D s s i f) Q)
  rw [map_sum (algebraMap ℝ ℂ)]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hA : i ∈ Q.1.1
  · by_cases hB : i ∈ Q.2.1
    · simp [downMove, hA, hB]
    · by_cases hb : 1 ≤ s <;> simp [downMove, hA, hB, hb, positionSign]
  · simp [downMove, hA]

private theorem sumDown_surjective_complex (D s : ℕ) (hs : 1 ≤ s) :
    Function.Surjective (sumDown (R := ℂ) D s s) := by
  classical
  intro y
  let yr : PairIndex D (s + 1) (s - 1) → ℝ := fun Q => (y Q).re
  let yi : PairIndex D (s + 1) (s - 1) → ℝ := fun Q => (y Q).im
  obtain ⟨xr, hxr⟩ := sumDown_surjective_real D s hs yr
  obtain ⟨xi, hxi⟩ := sumDown_surjective_real D s hs yi
  refine ⟨fun P => (xr P : ℂ) + Complex.I * (xi P : ℂ), ?_⟩
  have hdecomp :
      sumDown (R := ℂ) D s s (fun P => (xr P : ℂ) + Complex.I * (xi P : ℂ)) =
        (fun Q => ((sumDown (R := ℝ) D s s xr Q : ℝ) : ℂ)) +
          Complex.I • (fun Q => ((sumDown (R := ℝ) D s s xi Q : ℝ) : ℂ)) := by
    change sumDown (R := ℂ) D s s
        ((fun P => (xr P : ℂ)) + Complex.I • (fun P => (xi P : ℂ))) = _
    rw [map_add, map_smul, sumDown_complex_ofReal, sumDown_complex_ofReal]
  rw [hdecomp, hxr, hxi]
  funext Q
  simp only [Pi.add_apply, Pi.smul_apply]
  change ((y Q).re : ℂ) + Complex.I * ((y Q).im : ℂ) = y Q
  calc
    ((y Q).re : ℂ) + Complex.I * ((y Q).im : ℂ) =
        ((y Q).re : ℂ) + ((y Q).im : ℂ) * Complex.I := by ring
    _ = y Q := Complex.re_add_im (y Q)

theorem transferMap_surjective_aux (D s : ℕ) (hs : 1 ≤ s) :
    Function.Surjective (transferMap D s) := by
  classical
  let bs := coordinateTensorBasis D s s
  let bt := coordinateTensorBasis D (s + 1) (s - 1)
  intro y
  obtain ⟨x, hx⟩ := sumDown_surjective_complex D s hs (bt.equivFun y)
  refine ⟨bs.equivFun.symm x, ?_⟩
  apply bt.equivFun.injective
  change transferCoord D s x = bt.equivFun y
  rw [transferCoord_eq_sumDown D s hs]
  exact hx

end Kraw.GLSurjAux
