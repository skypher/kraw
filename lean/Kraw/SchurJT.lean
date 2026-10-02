import Kraw.Schur

/-!
# The dual Jacobi–Trudi identity for two-column shapes

Paper Proposition 1.3 (proof), citing Macdonald, Ch. I, (3.5): for the shape whose conjugate is
`(a, b)`, `s_λ = det [[e_a, e_{a+1}], [e_{b-1}, e_b]]`.
-/

open MvPolynomial
open Finset
open Classical

namespace Kraw

private def colZeroCell (a b : ℕ) (hba : b ≤ a) (i : Fin a) :
    (twoCol a b hba).cells :=
  ⟨(i.1, 0), by simp [twoCol]⟩

private def colOneCell (a b : ℕ) (hba : b ≤ a) (i : Fin b) :
    (twoCol a b hba).cells :=
  ⟨(i.1, 1), by simp [twoCol]⟩

private noncomputable def twoColCellEquiv (a b : ℕ) (hba : b ≤ a) :
    Sum (Fin a) (Fin b) ≃ (twoCol a b hba).cells := by
  classical
  let f : Sum (Fin a) (Fin b) → (twoCol a b hba).cells :=
    Sum.elim (colZeroCell a b hba) (colOneCell a b hba)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        have hv := congrArg Subtype.val h
        have hr := congrArg Prod.fst hv
        exact congrArg Sum.inl (Fin.ext hr)
      | inr j =>
        have hv := congrArg Subtype.val h
        have hc := congrArg Prod.snd hv
        norm_num [f, colZeroCell, colOneCell] at hc
    | inr i =>
      cases y with
      | inl j =>
        have hv := congrArg Subtype.val h
        have hc := congrArg Prod.snd hv
        norm_num [f, colZeroCell, colOneCell] at hc
      | inr j =>
        have hv := congrArg Subtype.val h
        have hr := congrArg Prod.fst hv
        exact congrArg Sum.inr (Fin.ext hr)
  · intro c
    rcases c with ⟨⟨r, j⟩, hc⟩
    have hmem : (r < a ∧ j = 0) ∨ (r < b ∧ j = 1) := by
      simpa [twoCol, Finset.mem_union, Finset.mem_product, eq_comm] using hc
    rcases hmem with ⟨hr, hj⟩ | ⟨hr, hj⟩
    · refine ⟨Sum.inl ⟨r, hr⟩, ?_⟩
      apply Subtype.ext
      simp [f, colZeroCell, hj]
    · refine ⟨Sum.inr ⟨r, hr⟩, ?_⟩
      apply Subtype.ext
      simp [f, colOneCell, hj]

private noncomputable def fillingToColumns (n a b : ℕ) (hba : b ≤ a) :
    ((twoCol a b hba).cells → Fin n) ≃ ((Fin a → Fin n) × (Fin b → Fin n)) :=
  (Equiv.arrowCongr (twoColCellEquiv a b hba).symm (Equiv.refl _)).trans
    (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) (Fin n))

private def twoColSeqValid {n : ℕ} (a b : ℕ) (hba : b ≤ a) (p :
    (Fin a → Fin n) × (Fin b → Fin n)) : Prop :=
  StrictMono p.1 ∧ StrictMono p.2 ∧
    ∀ i : Fin b, p.1 (i.castLE hba) ≤ p.2 i

private theorem fillingToColumns_colZero (n a b : ℕ) (hba : b ≤ a)
    (f : (twoCol a b hba).cells → Fin n) (i : Fin a) :
    (fillingToColumns n a b hba f).1 i = f (colZeroCell a b hba i) := by
  rfl

private theorem fillingToColumns_colOne (n a b : ℕ) (hba : b ≤ a)
    (f : (twoCol a b hba).cells → Fin n) (i : Fin b) :
    (fillingToColumns n a b hba f).2 i = f (colOneCell a b hba i) := by
  rfl

private theorem twoCol_isSemistandard_iff (n a b : ℕ) (hba : b ≤ a)
    (f : (twoCol a b hba).cells → Fin n) :
    IsSemistandard (twoCol a b hba) f ↔
      twoColSeqValid a b hba (fillingToColumns n a b hba f) := by
  classical
  constructor
  · rintro ⟨hrow, hcol⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      have h := hcol (colZeroCell a b hba i) (colZeroCell a b hba j) rfl
        (by simpa [colZeroCell] using hij)
      simpa only [fillingToColumns_colZero] using h
    · intro i j hij
      have h := hcol (colOneCell a b hba i) (colOneCell a b hba j) rfl
        (by simpa [colOneCell] using hij)
      simpa only [fillingToColumns_colOne] using h
    · intro i
      have h := hrow (colZeroCell a b hba (i.castLE hba)) (colOneCell a b hba i)
        rfl (by simp [colZeroCell, colOneCell])
      simpa only [fillingToColumns_colZero, fillingToColumns_colOne] using h
  · rintro ⟨hA, hB, hAB⟩
    refine ⟨?_, ?_⟩
    · intro c d hrow hcol
      rcases c with ⟨⟨r, j⟩, hc⟩
      rcases d with ⟨⟨s, k⟩, hd⟩
      change r = s at hrow
      change j ≤ k at hcol
      have hcm : (r < a ∧ j = 0) ∨ (r < b ∧ j = 1) := by
        simpa [twoCol, Finset.mem_union, Finset.mem_product, eq_comm] using hc
      have hdm : (s < a ∧ k = 0) ∨ (s < b ∧ k = 1) := by
        simpa [twoCol, Finset.mem_union, Finset.mem_product, eq_comm] using hd
      rcases hcm with ⟨hr, rfl⟩ | ⟨hr, rfl⟩ <;>
        rcases hdm with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
      · have : r = s := hrow
        subst s
        rfl
      · have hi : r < b := by omega
        have := hAB ⟨r, hi⟩
        subst s
        have hcast : (⟨r, hi⟩ : Fin b).castLE hba = ⟨r, hr⟩ := by
          apply Fin.ext
          rfl
        have ec : colZeroCell a b hba ⟨r, hr⟩ = ⟨(r, 0), hc⟩ := rfl
        have ed : colOneCell a b hba ⟨r, hi⟩ = ⟨(r, 1), hd⟩ := rfl
        simpa only [fillingToColumns_colZero, fillingToColumns_colOne, hcast, ec, ed] using this
      · omega
      · have : r = s := hrow
        subst s
        rfl
    · intro c d hcol hrow
      rcases c with ⟨⟨r, j⟩, hc⟩
      rcases d with ⟨⟨s, k⟩, hd⟩
      change j = k at hcol
      change r < s at hrow
      have hcm : (r < a ∧ j = 0) ∨ (r < b ∧ j = 1) := by
        simpa [twoCol, Finset.mem_union, Finset.mem_product, eq_comm] using hc
      have hdm : (s < a ∧ k = 0) ∨ (s < b ∧ k = 1) := by
        simpa [twoCol, Finset.mem_union, Finset.mem_product, eq_comm] using hd
      rcases hcm with ⟨hr, rfl⟩ | ⟨hr, rfl⟩ <;>
        rcases hdm with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
      · have hij : (⟨r, hr⟩ : Fin a) < ⟨s, hs⟩ := by
          rw [Fin.lt_def]
          exact hrow
        have := hA hij
        simpa only [fillingToColumns_colZero, colZeroCell] using this
      · omega
      · omega
      · have hij : (⟨r, hr⟩ : Fin b) < ⟨s, hs⟩ := by
          rw [Fin.lt_def]
          exact hrow
        have := hB hij
        simpa only [fillingToColumns_colOne, colOneCell] using this

private noncomputable def twoColWeight (n a b : ℕ) (p :
    (Fin a → Fin n) × (Fin b → Fin n)) : MvPolynomial (Fin n) ℤ :=
  (∏ i : Fin a, X (p.1 i)) * ∏ i : Fin b, X (p.2 i)

private theorem fillingWeight_eq_twoColWeight (n a b : ℕ) (hba : b ≤ a)
    (f : (twoCol a b hba).cells → Fin n) :
    (∏ c : (twoCol a b hba).cells, X (f c)) =
      twoColWeight n a b (fillingToColumns n a b hba f) := by
  classical
  unfold twoColWeight
  calc
    (∏ c : (twoCol a b hba).cells, X (f c)) =
        ∏ i : Sum (Fin a) (Fin b), X (f (twoColCellEquiv a b hba i)) := by
      symm
      exact Fintype.prod_equiv (twoColCellEquiv a b hba)
        (fun i => X (f (twoColCellEquiv a b hba i))) (fun c => X (f c)) (fun _ => rfl)
    _ = (∏ i : Fin a, X (f (colZeroCell a b hba i))) *
          ∏ i : Fin b, X (f (colOneCell a b hba i)) := by
      rw [Fintype.prod_sum_type]
      change (∏ i : Fin a, X (f (colZeroCell a b hba i))) *
          ∏ i : Fin b, X (f (colOneCell a b hba i)) = _
      rfl
    _ = (∏ i : Fin a, X ((fillingToColumns n a b hba f).1 i)) *
          ∏ i : Fin b, X ((fillingToColumns n a b hba f).2 i) := by
      simp only [fillingToColumns_colZero, fillingToColumns_colOne]

private theorem schur_eq_twoColSeqSum (n a b : ℕ) (hba : b ≤ a) :
    schur (twoCol a b hba) n =
      ∑ p ∈ Finset.univ.filter (twoColSeqValid a b hba), twoColWeight n a b p := by
  classical
  unfold schur
  refine Finset.sum_equiv (fillingToColumns n a b hba) ?_ ?_
  · intro f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (twoCol_isSemistandard_iff n a b hba f)
  · intro f hf
    exact fillingWeight_eq_twoColWeight n a b hba f

private noncomputable def strictSeqFinsetEquiv (k n : ℕ) :
    {f : Fin k → Fin n // StrictMono f} ≃ {s : Finset (Fin n) // s.card = k} := by
  classical
  refine
    { toFun := fun f => ⟨Finset.univ.image f.1, ?_⟩
      invFun := fun s => ⟨s.1.orderEmbOfFin s.2, (s.1.orderEmbOfFin s.2).strictMono⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [Finset.card_image_of_injective _ f.2.injective]
    simp
  · intro f
    apply Subtype.ext
    have hc : (Finset.univ.image f.1).card = k := by
      rw [Finset.card_image_of_injective _ f.2.injective]
      simp
    exact (Finset.orderEmbOfFin_unique hc (by intro i; simp) f.2).symm
  · intro s
    apply Subtype.ext
    simp

private theorem strictSeqWeight_eq_finsetWeight (n k : ℕ)
    (f : {f : Fin k → Fin n // StrictMono f}) :
    (∏ i : Fin k, X (f.1 i)) =
      ∏ i ∈ (strictSeqFinsetEquiv k n f).1, (X i : MvPolynomial (Fin n) ℤ) := by
  classical
  change (∏ i : Fin k, X (f.1 i)) =
    ∏ i ∈ Finset.univ.image f.1, (X i : MvPolynomial (Fin n) ℤ)
  symm
  rw [Finset.prod_image f.2.injective.injOn]

private theorem strictSeqSum_eq_esymm (n k : ℕ) :
    (∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin n => StrictMono f),
      ∏ i : Fin k, X (f i)) = esymm (Fin n) ℤ k := by
  classical
  rw [← Finset.sum_subtype_eq_sum_filter]
  rw [Finset.subtype_univ]
  change (∑ f : {f : Fin k → Fin n // StrictMono f},
    ∏ i : Fin k, X (f.1 i)) = _
  rw [MvPolynomial.esymm_eq_sum_subtype]
  refine Fintype.sum_equiv (strictSeqFinsetEquiv k n)
    (fun f => ∏ i : Fin k, X (f.1 i))
    (fun s => ∏ i ∈ s.1, X i) ?_
  intro f
  exact strictSeqWeight_eq_finsetWeight n k f

private def twoColDominates {n : ℕ} (A B : Finset (Fin n)) : Prop :=
  ∀ t : Fin n, (B.filter (fun i => i ≤ t)).card ≤ (A.filter (fun i => i ≤ t)).card

private theorem image_prefix_card (n k : ℕ) (f : Fin k → Fin n)
    (hf : StrictMono f) (t : Fin n) :
    ((Finset.univ.image f).filter (fun x => x ≤ t)).card =
      (Finset.univ.filter (fun i => f i ≤ t)).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ hf.injective]

private theorem twoCol_pointwise_iff_dominates (n a b : ℕ) (hba : b ≤ a)
    (f : Fin a → Fin n) (g : Fin b → Fin n) (hf : StrictMono f) (hg : StrictMono g) :
    (∀ i : Fin b, f (i.castLE hba) ≤ g i) ↔
      twoColDominates (Finset.univ.image f) (Finset.univ.image g) := by
  classical
  constructor
  · intro hfg t
    rw [image_prefix_card n b g hg t, image_prefix_card n a f hf t]
    let sb := Finset.univ.filter (fun i : Fin b => g i ≤ t)
    let sa := Finset.univ.filter (fun i : Fin a => f i ≤ t)
    have hsub : sb.image (fun i : Fin b => i.castLE hba) ⊆ sa := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      simp only [sb, sa, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact (hfg i).trans hi
    have hcard := Finset.card_le_card hsub
    have hinj : Function.Injective (fun i : Fin b => i.castLE hba) := by
      intro i j hij
      apply Fin.ext
      simpa using congrArg Fin.val hij
    rwa [Finset.card_image_of_injective _ hinj] at hcard
  · intro hdom i
    by_contra! hfail
    let t := g i
    let sb := Finset.univ.filter (fun j : Fin b => g j ≤ t)
    let sa := Finset.univ.filter (fun j : Fin a => f j ≤ t)
    have hBsub : Finset.Iic i ⊆ sb := by
      intro j hj
      simp only [sb, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hg.monotone (Finset.mem_Iic.mp hj)
    have hAsub : sa ⊆ Finset.Iio (i.castLE hba) := by
      intro j hj
      simp only [sa, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Iio]
      by_contra hjnot
      have hij : i.castLE hba ≤ j := le_of_not_gt hjnot
      have hmono := hf.monotone hij
      exact (not_le_of_gt hfail) (hmono.trans hj)
    have hBcard : i.val + 1 ≤ sb.card := by
      have := Finset.card_le_card hBsub
      simpa [sb] using this
    have hAcard : sa.card ≤ i.val := by
      have := Finset.card_le_card hAsub
      simpa [sa] using this
    have hcounts : sb.card ≤ sa.card := by
      calc
        sb.card = ((Finset.univ.image g).filter (fun x => x ≤ t)).card :=
          (image_prefix_card n b g hg t).symm
        _ ≤ ((Finset.univ.image f).filter (fun x => x ≤ t)).card := hdom t
        _ = sa.card := image_prefix_card n a f hf t
    omega

private theorem twoColSeqValid_iff_dominates (n a b : ℕ) (hba : b ≤ a)
    (p : (Fin a → Fin n) × (Fin b → Fin n)) :
    twoColSeqValid a b hba p ↔
      ∃ hf : StrictMono p.1, ∃ hg : StrictMono p.2,
        twoColDominates (Finset.univ.image p.1) (Finset.univ.image p.2) := by
  constructor
  · rintro ⟨hf, hg, hfg⟩
    exact ⟨hf, hg, (twoCol_pointwise_iff_dominates n a b hba p.1 p.2 hf hg).mp hfg⟩
  · rintro ⟨hf, hg, hdom⟩
    exact ⟨hf, hg, (twoCol_pointwise_iff_dominates n a b hba p.1 p.2 hf hg).mpr hdom⟩

private abbrev TwoColPairSets (n a b : ℕ) :=
  ({A : Finset (Fin n) // A.card = a} × {B : Finset (Fin n) // B.card = b})

private def twoColPairGood {n a b : ℕ} (p : TwoColPairSets n a b) : Prop :=
  twoColDominates p.1.1 p.2.1

private noncomputable def twoColPairWeight (n a b : ℕ) (p : TwoColPairSets n a b) :
    MvPolynomial (Fin n) ℤ :=
  (∏ i ∈ p.1.1, X i) * ∏ i ∈ p.2.1, X i

private noncomputable def seqGoodFinsetEquiv (n a b : ℕ) (hba : b ≤ a) :
    {p : (Fin a → Fin n) × (Fin b → Fin n) // twoColSeqValid a b hba p} ≃
      {p : TwoColPairSets n a b // twoColPairGood p} := by
  classical
  let eA := strictSeqFinsetEquiv a n
  let eB := strictSeqFinsetEquiv b n
  refine
    { toFun := fun p => ⟨(eA ⟨p.1.1, p.2.1⟩, eB ⟨p.1.2, p.2.2.1⟩), ?_⟩
      invFun := fun p => ⟨(eA.symm p.1.1, eB.symm p.1.2), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change twoColDominates (Finset.univ.image p.1.1) (Finset.univ.image p.1.2)
    exact (twoCol_pointwise_iff_dominates n a b hba p.1.1 p.1.2 p.2.1 p.2.2.1).mp
      p.2.2.2
  · rcases p with ⟨⟨⟨A, hA⟩, ⟨B, hB⟩⟩, hdom⟩
    let u := eA.symm ⟨A, hA⟩
    let v := eB.symm ⟨B, hB⟩
    refine ⟨u.2, v.2, ?_⟩
    have hu : Finset.univ.image u.1 = A := by
      simpa [u, eA, strictSeqFinsetEquiv] using Finset.image_orderEmbOfFin_univ A hA
    have hv : Finset.univ.image v.1 = B := by
      simpa [v, eB, strictSeqFinsetEquiv] using Finset.image_orderEmbOfFin_univ B hB
    change twoColDominates A B at hdom
    exact (twoCol_pointwise_iff_dominates n a b hba u.1 v.1 u.2 v.2).mpr
      (by simpa [hu, hv] using hdom)
  · intro p
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (eA.symm_apply_apply ⟨p.1.1, p.2.1⟩)
    · exact congrArg Subtype.val (eB.symm_apply_apply ⟨p.1.2, p.2.2.1⟩)
  · intro p
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Subtype.val (eA.apply_symm_apply p.1.1)
    · apply Subtype.ext
      exact congrArg Subtype.val (eB.apply_symm_apply p.1.2)

private theorem twoColWeight_eq_pairWeight (n a b : ℕ) (hba : b ≤ a)
    (p : {p : (Fin a → Fin n) × (Fin b → Fin n) // twoColSeqValid a b hba p}) :
    twoColWeight n a b p.1 = twoColPairWeight n a b (seqGoodFinsetEquiv n a b hba p).1 := by
  classical
  change
    ((∏ i : Fin a, X (p.1.1 i)) * ∏ i : Fin b, X (p.1.2 i)) =
      (∏ i ∈ (strictSeqFinsetEquiv a n ⟨p.1.1, p.2.1⟩).1, X i) *
        ∏ i ∈ (strictSeqFinsetEquiv b n ⟨p.1.2, p.2.2.1⟩).1, X i
  exact congrArg₂ (· * ·)
    (strictSeqWeight_eq_finsetWeight n a ⟨p.1.1, p.2.1⟩)
    (strictSeqWeight_eq_finsetWeight n b ⟨p.1.2, p.2.2.1⟩)

private theorem schur_eq_goodPairSum (n a b : ℕ) (hba : b ≤ a) :
    schur (twoCol a b hba) n =
      ∑ p ∈ Finset.univ.filter (twoColPairGood (n := n) (a := a) (b := b)),
        twoColPairWeight n a b p := by
  classical
  rw [schur_eq_twoColSeqSum n a b hba]
  rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  refine Fintype.sum_equiv (seqGoodFinsetEquiv n a b hba)
    (fun p => twoColWeight n a b p.1)
    (fun p => twoColPairWeight n a b p.1) ?_
  intro p
  exact twoColWeight_eq_pairWeight n a b hba p

private def leftPart {n : ℕ} (s : Finset (Fin n)) (t : Fin n) : Finset (Fin n) :=
  s.filter (fun x => x ≤ t)

private def rightPart {n : ℕ} (s : Finset (Fin n)) (t : Fin n) : Finset (Fin n) :=
  s.filter (fun x => t < x)

private def prefixSize {n : ℕ} (s : Finset (Fin n)) (t : Fin n) : ℕ :=
  (leftPart s t).card

private def beforeSize {n : ℕ} (s : Finset (Fin n)) (t : Fin n) : ℕ :=
  (s.filter (fun x => x < t)).card

private def crossings {n : ℕ} (A B : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun t => prefixSize A t > prefixSize B t)

private noncomputable def firstCross {n : ℕ} (A B : Finset (Fin n))
    (h : (crossings A B).Nonempty) : Fin n := (crossings A B).min' h

private theorem firstCross_mem {n : ℕ} (A B : Finset (Fin n))
    (h : (crossings A B).Nonempty) : firstCross A B h ∈ crossings A B :=
  Finset.min'_mem _ _

private theorem firstCross_le_mem {n : ℕ} (A B : Finset (Fin n))
    (h : (crossings A B).Nonempty) {u : Fin n} (hu : u ∈ crossings A B) :
    firstCross A B h ≤ u := (crossings A B).min'_le u hu

private theorem leftPart_eq_inter_Iic {n : ℕ} (s : Finset (Fin n)) (t : Fin n) :
    leftPart s t = s ∩ Finset.Iic t := by
  ext x
  simp [leftPart, Finset.mem_filter, Finset.mem_inter, Finset.mem_Iic]

private theorem beforeSize_eq_inter_Iio {n : ℕ} (s : Finset (Fin n)) (t : Fin n) :
    beforeSize s t = (s ∩ Finset.Iio t).card := by
  unfold beforeSize
  rw [show s.filter (fun x => x < t) = s ∩ Finset.Iio t by
    ext x
    simp [Finset.mem_filter, Finset.mem_inter, Finset.mem_Iio]]

private theorem prefix_before_le_add_one {n : ℕ} (s : Finset (Fin n)) (t : Fin n) :
    prefixSize s t ≤ beforeSize s t + 1 := by
  have hsub : leftPart s t ⊆ insert t (s.filter (fun x => x < t)) := by
    intro x hx
    simp only [leftPart, Finset.mem_filter] at hx
    rcases le_iff_lt_or_eq.mp hx.2 with hlt | heq
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx.1, hlt⟩)
    · simpa [heq]
  calc
    prefixSize s t ≤ (insert t (s.filter (fun x => x < t))).card := Finset.card_le_card hsub
    _ ≤ beforeSize s t + 1 := by simp [prefixSize, beforeSize, Finset.card_insert_le]

private theorem before_le_prefix {n : ℕ} (s : Finset (Fin n)) (t : Fin n) :
    beforeSize s t ≤ prefixSize s t := by
  apply Finset.card_le_card
  intro x hx
  simp only [beforeSize, prefixSize, leftPart, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, le_of_lt hx.2⟩

private theorem firstCross_before_le {n : ℕ} (A B : Finset (Fin n))
    (h : (crossings A B).Nonempty) :
    beforeSize A (firstCross A B h) ≤ beforeSize B (firstCross A B h) := by
  let t := firstCross A B h
  letI := t.neZero
  by_cases ht : t = 0
  · simp [beforeSize, t, ht]
  · have htpos : 0 < t := Fin.pos_iff_ne_zero.mpr ht
    have hprevlt : t - 1 < t := by
      rw [Fin.lt_def, Fin.val_sub_one_of_ne_zero ht]
      omega
    have hprevnot : t - 1 ∉ crossings A B := by
      intro hp
      have hle := firstCross_le_mem A B h hp
      exact (not_lt_of_ge hle) hprevlt
    have hprevle : prefixSize A (t - 1) ≤ prefixSize B (t - 1) := by
      by_contra hgt
      have hstrict : prefixSize B (t - 1) < prefixSize A (t - 1) :=
        Nat.lt_of_not_ge hgt
      have hp : t - 1 ∈ crossings A B := by
        simp only [crossings, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hstrict
      exact hprevnot hp
    have hrewrite : Finset.Iic (t - 1) = Finset.Iio t :=
      Fin.Iic_sub_one_eq_Iio (b := t) htpos
    have hprevle' : beforeSize A t ≤ beforeSize B t := by
      change (leftPart A (t - 1)).card ≤ (leftPart B (t - 1)).card at hprevle
      simp only [leftPart_eq_inter_Iic, hrewrite] at hprevle
      rw [beforeSize_eq_inter_Iio, beforeSize_eq_inter_Iio]
      exact hprevle
    simpa [t] using hprevle'

private theorem firstCross_prefix_eq_succ {n : ℕ} (A B : Finset (Fin n))
    (h : (crossings A B).Nonempty) :
    prefixSize A (firstCross A B h) = prefixSize B (firstCross A B h) + 1 := by
  let t := firstCross A B h
  have hcross := (Finset.mem_filter.mp (firstCross_mem A B h)).2
  have hbefore := firstCross_before_le A B h
  have hA := prefix_before_le_add_one A t
  have hB := before_le_prefix B t
  simp only [t] at hcross hbefore hA hB ⊢
  omega

private theorem no_cross_before_first {n : ℕ} (A B : Finset (Fin n))
    (h : (crossings A B).Nonempty) {u : Fin n}
    (hu : u < firstCross A B h) :
    prefixSize A u ≤ prefixSize B u := by
  by_contra hbad
  have hlt : prefixSize B u < prefixSize A u := Nat.lt_of_not_ge hbad
  have hmem : u ∈ crossings A B := by
    simp only [crossings, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hlt
  exact (not_lt_of_ge (firstCross_le_mem A B h hmem)) hu

private theorem leftRight_disjoint {n : ℕ} (s : Finset (Fin n)) (t : Fin n) :
    Disjoint (leftPart s t) (rightPart s t) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [leftPart, rightPart, Finset.mem_filter] at hx hy
  exact (not_lt_of_ge hx.2) hy.2

private theorem leftRight_union {n : ℕ} (s : Finset (Fin n)) (t : Fin n) :
    leftPart s t ∪ rightPart s t = s := by
  ext x
  simp only [Finset.mem_union, leftPart, rightPart, Finset.mem_filter]
  constructor
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  · intro hx
    rcases lt_or_ge t x with htx | hxt
    · exact Or.inr ⟨hx, htx⟩
    · exact Or.inl ⟨hx, hxt⟩

private theorem leftRight_card {n : ℕ} (s : Finset (Fin n)) (t : Fin n) :
    (leftPart s t).card + (rightPart s t).card = s.card := by
  calc
    (leftPart s t).card + (rightPart s t).card =
        (leftPart s t ∪ rightPart s t).card := by
      rw [Finset.card_union_of_disjoint (leftRight_disjoint s t)]
    _ = s.card := congrArg Finset.card (leftRight_union s t)

private def tailSwapPair {n : ℕ} (A B : Finset (Fin n)) (t : Fin n) :
    Finset (Fin n) × Finset (Fin n) :=
  (leftPart B t ∪ rightPart A t, leftPart A t ∪ rightPart B t)

private theorem leftPart_leftUnionRight {n : ℕ} (s r : Finset (Fin n)) (t : Fin n) :
    leftPart (leftPart s t ∪ rightPart r t) t = leftPart s t := by
  ext x
  simp only [leftPart, rightPart, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨(⟨hx, hxt⟩ | ⟨hx, htx⟩), hxt'⟩
    · exact ⟨hx, hxt⟩
    · exact False.elim ((not_lt_of_ge hxt') htx)
  · rintro ⟨hx, hxt⟩
    exact ⟨Or.inl ⟨hx, hxt⟩, hxt⟩

private theorem rightPart_leftUnionRight {n : ℕ} (s r : Finset (Fin n)) (t : Fin n) :
    rightPart (leftPart s t ∪ rightPart r t) t = rightPart r t := by
  ext x
  simp only [leftPart, rightPart, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨(⟨hx, hxt⟩ | ⟨hx, htx⟩), htx'⟩
    · exact False.elim ((not_lt_of_ge hxt) htx')
    · exact ⟨hx, htx⟩
  · rintro ⟨hx, htx⟩
    exact ⟨Or.inr ⟨hx, htx⟩, htx⟩

private theorem tailSwapPair_involutive {n : ℕ} (A B : Finset (Fin n)) (t : Fin n) :
    tailSwapPair (tailSwapPair A B t).1 (tailSwapPair A B t).2 t = (A, B) := by
  apply Prod.ext
  · change leftPart (leftPart A t ∪ rightPart B t) t ∪
        rightPart (leftPart B t ∪ rightPart A t) t = A
    rw [leftPart_leftUnionRight, rightPart_leftUnionRight, leftRight_union]
  · change leftPart (leftPart B t ∪ rightPart A t) t ∪
        rightPart (leftPart A t ∪ rightPart B t) t = B
    rw [leftPart_leftUnionRight, rightPart_leftUnionRight, leftRight_union]

private theorem tailSwapPair_card {n : ℕ} {a b : ℕ} (A B : Finset (Fin n))
    (hA : A.card = a) (hB : B.card = b) (t : Fin n)
    (hcross : prefixSize B t = prefixSize A t + 1) :
    (tailSwapPair A B t).1.card = a + 1 ∧
      (tailSwapPair A B t).2.card + 1 = b := by
  have hdis₁ : Disjoint (leftPart B t) (rightPart A t) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [leftPart, rightPart, Finset.mem_filter] at hx hy
    exact (not_lt_of_ge hx.2) hy.2
  have hdis₂ : Disjoint (leftPart A t) (rightPart B t) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [leftPart, rightPart, Finset.mem_filter] at hx hy
    exact (not_lt_of_ge hx.2) hy.2
  have hAparts := leftRight_card A t
  have hBparts := leftRight_card B t
  change (leftPart B t).card = (leftPart A t).card + 1 at hcross
  have hswapA : (tailSwapPair A B t).1.card =
      (leftPart B t).card + (rightPart A t).card := by
    simp [tailSwapPair, Finset.card_union_of_disjoint hdis₁]
  have hswapB : (tailSwapPair A B t).2.card =
      (leftPart A t).card + (rightPart B t).card := by
    simp [tailSwapPair, Finset.card_union_of_disjoint hdis₂]
  constructor
  · rw [hswapA]
    omega
  · rw [hswapB]
    omega

private theorem tailSwapPair_card_reverse {n : ℕ} {a b : ℕ} (A B : Finset (Fin n))
    (hA : A.card = a) (hB : B.card = b) (t : Fin n)
    (hcross : prefixSize A t = prefixSize B t + 1) :
    (tailSwapPair A B t).1.card + 1 = a ∧
      (tailSwapPair A B t).2.card = b + 1 := by
  have hdis₁ : Disjoint (leftPart B t) (rightPart A t) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [leftPart, rightPart, Finset.mem_filter] at hx hy
    exact (not_lt_of_ge hx.2) hy.2
  have hdis₂ : Disjoint (leftPart A t) (rightPart B t) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [leftPart, rightPart, Finset.mem_filter] at hx hy
    exact (not_lt_of_ge hx.2) hy.2
  have hAparts := leftRight_card A t
  have hBparts := leftRight_card B t
  change (leftPart A t).card = (leftPart B t).card + 1 at hcross
  have hswapA : (tailSwapPair A B t).1.card =
      (leftPart B t).card + (rightPart A t).card := by
    simp [tailSwapPair, Finset.card_union_of_disjoint hdis₁]
  have hswapB : (tailSwapPair A B t).2.card =
      (leftPart A t).card + (rightPart B t).card := by
    simp [tailSwapPair, Finset.card_union_of_disjoint hdis₂]
  constructor
  · rw [hswapA]
    omega
  · rw [hswapB]
    omega

private theorem crossings_nonempty_of_card_gt {n : ℕ} (A B : Finset (Fin n))
    (hcard : B.card < A.card) : (crossings A B).Nonempty := by
  classical
  have hApos : 0 < A.card := lt_of_le_of_lt (Nat.zero_le _) hcard
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hApos
  have hunion : (A ∪ B).Nonempty := ⟨x, Finset.mem_union.mpr (Or.inl hx)⟩
  let t := (A ∪ B).max' hunion
  have hAall : leftPart A t = A := by
    ext y
    simp only [leftPart, Finset.mem_filter]
    constructor
    · exact And.left
    · intro hy
      exact ⟨hy, Finset.le_max' (A ∪ B) y (Finset.mem_union.mpr (Or.inl hy))⟩
  have hBall : leftPart B t = B := by
    ext y
    simp only [leftPart, Finset.mem_filter]
    constructor
    · exact And.left
    · intro hy
      exact ⟨hy, Finset.le_max' (A ∪ B) y (Finset.mem_union.mpr (Or.inr hy))⟩
  refine ⟨t, ?_⟩
  simp only [crossings, Finset.mem_filter, Finset.mem_univ, true_and]
  change (leftPart A t).card > (leftPart B t).card
  rw [hAall, hBall]
  exact hcard

private theorem crossings_nonempty_of_not_dominates {n : ℕ} (A B : Finset (Fin n))
    (h : ¬ twoColDominates A B) : (crossings B A).Nonempty := by
  classical
  unfold twoColDominates at h
  push_neg at h
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  simp only [crossings, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ht

private theorem prefixSize_swap_first_of_le {n : ℕ} (A B : Finset (Fin n))
    (u t : Fin n) (hu : u ≤ t) :
    prefixSize (tailSwapPair A B t).1 u = prefixSize B u := by
  have hset : leftPart (leftPart B t ∪ rightPart A t) u = leftPart B u := by
    ext x
    simp only [leftPart, rightPart, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨(⟨hx, _⟩ | ⟨_, htx⟩), hxu⟩
      · exact ⟨hx, hxu⟩
      · exact False.elim ((not_lt_of_ge (hxu.trans hu)) htx)
    · rintro ⟨hx, hxu⟩
      exact ⟨Or.inl ⟨hx, hxu.trans hu⟩, hxu⟩
  exact congrArg Finset.card hset

private theorem prefixSize_swap_second_of_le {n : ℕ} (A B : Finset (Fin n))
    (u t : Fin n) (hu : u ≤ t) :
    prefixSize (tailSwapPair A B t).2 u = prefixSize A u := by
  have hset : leftPart (leftPart A t ∪ rightPart B t) u = leftPart A u := by
    ext x
    simp only [leftPart, rightPart, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨(⟨hx, _⟩ | ⟨_, htx⟩), hxu⟩
      · exact ⟨hx, hxu⟩
      · exact False.elim ((not_lt_of_ge (hxu.trans hu)) htx)
    · rintro ⟨hx, hxu⟩
      exact ⟨Or.inl ⟨hx, hxu.trans hu⟩, hxu⟩
  exact congrArg Finset.card hset

private theorem tailSwap_firstCross_eq {n : ℕ} (A B : Finset (Fin n)) (t : Fin n)
    (hcross : prefixSize B t = prefixSize A t + 1)
    (hminimal : ∀ u : Fin n, u < t → prefixSize B u ≤ prefixSize A u)
    (hnonempty : (crossings (tailSwapPair A B t).1 (tailSwapPair A B t).2).Nonempty) :
    firstCross (tailSwapPair A B t).1 (tailSwapPair A B t).2
      hnonempty = t := by
  let C := tailSwapPair A B t
  have hmem : t ∈ crossings C.1 C.2 := by
    simp only [crossings, Finset.mem_filter, Finset.mem_univ, true_and]
    change (leftPart (leftPart B t ∪ rightPart A t) t).card >
      (leftPart (leftPart A t ∪ rightPart B t) t).card
    rw [leftPart_leftUnionRight, leftPart_leftUnionRight]
    change (leftPart B t).card > (leftPart A t).card
    change (leftPart B t).card = (leftPart A t).card + 1 at hcross
    omega
  apply le_antisymm
  · exact firstCross_le_mem C.1 C.2 hnonempty hmem
  · by_contra hnot
    let u := firstCross C.1 C.2 hnonempty
    have hut : u < t := lt_of_not_ge hnot
    have hmin := hminimal u hut
    have hfirst := firstCross_mem C.1 C.2 hnonempty
    have hcrossu := (Finset.mem_filter.mp hfirst).2
    have hswap₁ := prefixSize_swap_first_of_le A B u t hut.le
    have hswap₂ := prefixSize_swap_second_of_le A B u t hut.le
    change prefixSize B u ≤ prefixSize A u at hmin
    rw [hswap₁, hswap₂] at hcrossu
    omega

private theorem tailSwapPair_crossings_nonempty {n : ℕ} (A B : Finset (Fin n))
    (h : (crossings B A).Nonempty) :
    (crossings (tailSwapPair A B (firstCross B A h)).1
      (tailSwapPair A B (firstCross B A h)).2).Nonempty := by
  let t := firstCross B A h
  refine ⟨t, ?_⟩
  simp only [crossings, Finset.mem_filter, Finset.mem_univ, true_and]
  change (leftPart (leftPart B t ∪ rightPart A t) t).card >
    (leftPart (leftPart A t ∪ rightPart B t) t).card
  rw [leftPart_leftUnionRight, leftPart_leftUnionRight]
  have hc := firstCross_prefix_eq_succ B A h
  change (leftPart B t).card = (leftPart A t).card + 1 at hc
  omega

private theorem tailSwapPair_firstCross_preserved {n : ℕ} (A B : Finset (Fin n))
    (h : (crossings B A).Nonempty) :
    firstCross (tailSwapPair A B (firstCross B A h)).1
      (tailSwapPair A B (firstCross B A h)).2
      (tailSwapPair_crossings_nonempty A B h) = firstCross B A h := by
  let t := firstCross B A h
  have hc := firstCross_prefix_eq_succ B A h
  have hmin : ∀ u : Fin n, u < t → prefixSize B u ≤ prefixSize A u := by
    intro u hu
    exact no_cross_before_first B A h hu
  change firstCross (tailSwapPair A B t).1 (tailSwapPair A B t).2
    (tailSwapPair_crossings_nonempty A B h) = t
  exact tailSwap_firstCross_eq A B t hc hmin (tailSwapPair_crossings_nonempty A B h)

private theorem tailSwapPair_weight {n : ℕ} (A B : Finset (Fin n)) (t : Fin n) :
    ((∏ i ∈ A, (X i : MvPolynomial (Fin n) ℤ)) *
        ∏ i ∈ B, (X i : MvPolynomial (Fin n) ℤ)) =
      (∏ i ∈ (tailSwapPair A B t).1, (X i : MvPolynomial (Fin n) ℤ)) *
        ∏ i ∈ (tailSwapPair A B t).2, (X i : MvPolynomial (Fin n) ℤ) := by
  have hA : (∏ i ∈ A, (X i : MvPolynomial (Fin n) ℤ)) =
      (∏ i ∈ leftPart A t, (X i : MvPolynomial (Fin n) ℤ)) *
        ∏ i ∈ rightPart A t, (X i : MvPolynomial (Fin n) ℤ) := by
    calc
      _ = ∏ i ∈ leftPart A t ∪ rightPart A t, (X i : MvPolynomial (Fin n) ℤ) :=
        congrArg (fun s : Finset (Fin n) =>
          ∏ i ∈ s, (X i : MvPolynomial (Fin n) ℤ)) (leftRight_union A t).symm
      _ = _ := Finset.prod_union (leftRight_disjoint A t)
  have hB : (∏ i ∈ B, (X i : MvPolynomial (Fin n) ℤ)) =
      (∏ i ∈ leftPart B t, (X i : MvPolynomial (Fin n) ℤ)) *
        ∏ i ∈ rightPart B t, (X i : MvPolynomial (Fin n) ℤ) := by
    calc
      _ = ∏ i ∈ leftPart B t ∪ rightPart B t, (X i : MvPolynomial (Fin n) ℤ) :=
        congrArg (fun s : Finset (Fin n) =>
          ∏ i ∈ s, (X i : MvPolynomial (Fin n) ℤ)) (leftRight_union B t).symm
      _ = _ := Finset.prod_union (leftRight_disjoint B t)
  have hC : (∏ i ∈ (tailSwapPair A B t).1, (X i : MvPolynomial (Fin n) ℤ)) =
      (∏ i ∈ leftPart B t, (X i : MvPolynomial (Fin n) ℤ)) *
        ∏ i ∈ rightPart A t, (X i : MvPolynomial (Fin n) ℤ) := by
    change (∏ i ∈ leftPart B t ∪ rightPart A t, (X i : MvPolynomial (Fin n) ℤ)) = _
    exact Finset.prod_union (by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      simp only [leftPart, rightPart, Finset.mem_filter] at hx hy
      exact (not_lt_of_ge hx.2) hy.2)
  have hD : (∏ i ∈ (tailSwapPair A B t).2, (X i : MvPolynomial (Fin n) ℤ)) =
      (∏ i ∈ leftPart A t, (X i : MvPolynomial (Fin n) ℤ)) *
        ∏ i ∈ rightPart B t, (X i : MvPolynomial (Fin n) ℤ) := by
    change (∏ i ∈ leftPart A t ∪ rightPart B t, (X i : MvPolynomial (Fin n) ℤ)) = _
    exact Finset.prod_union (by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      simp only [leftPart, rightPart, Finset.mem_filter] at hx hy
      exact (not_lt_of_ge hx.2) hy.2)
  rw [hA, hB, hC, hD]
  ring

private noncomputable def badPairToShifted {n a b : ℕ}
    (p : {p : TwoColPairSets n a b // ¬ twoColPairGood p}) :
    TwoColPairSets n (a + 1) (b - 1) := by
  classical
  let A := p.1.1.1
  let B := p.1.2.1
  let hc := crossings_nonempty_of_not_dominates A B p.2
  let t := firstCross B A hc
  have hcross := firstCross_prefix_eq_succ B A hc
  have hcards := tailSwapPair_card A B p.1.1.2 p.1.2.2 t hcross
  refine ⟨⟨(tailSwapPair A B t).1, hcards.1⟩,
    ⟨(tailSwapPair A B t).2, ?_⟩⟩
  omega

private noncomputable def shiftedToBad {n a b : ℕ} (hba : b ≤ a) (hb : 1 ≤ b)
    (q : TwoColPairSets n (a + 1) (b - 1)) :
    {p : TwoColPairSets n a b // ¬ twoColPairGood p} := by
  classical
  let C := q.1.1
  let D := q.2.1
  have hcard : D.card < C.card := by
    change q.2.1.card < q.1.1.card
    rw [q.2.2, q.1.2]
    omega
  let hc := crossings_nonempty_of_card_gt C D hcard
  let t := firstCross C D hc
  have hcross := firstCross_prefix_eq_succ C D hc
  have hcards := tailSwapPair_card_reverse C D q.1.2 q.2.2 t hcross
  have hA : (tailSwapPair C D t).1.card = a := by omega
  have hB : (tailSwapPair C D t).2.card = b := by omega
  let p : TwoColPairSets n a b :=
    (⟨(tailSwapPair C D t).1, hA⟩, ⟨(tailSwapPair C D t).2, hB⟩)
  refine ⟨p, ?_⟩
  intro hgood
  have hdom := hgood t
  change prefixSize (tailSwapPair C D t).2 t ≤
    prefixSize (tailSwapPair C D t).1 t at hdom
  have hsecond : prefixSize (tailSwapPair C D t).2 t = prefixSize C t := by
    change (leftPart (leftPart C t ∪ rightPart D t) t).card = prefixSize C t
    rw [leftPart_leftUnionRight]
    rfl
  have hfirst : prefixSize (tailSwapPair C D t).1 t = prefixSize D t := by
    change (leftPart (leftPart D t ∪ rightPart C t) t).card = prefixSize D t
    rw [leftPart_leftUnionRight]
    rfl
  rw [hsecond, hfirst] at hdom
  change prefixSize C t = prefixSize D t + 1 at hcross
  omega

private noncomputable def badPairTailSwapEquiv {n a b : ℕ} (hba : b ≤ a) (hb : 1 ≤ b) :
    {p : TwoColPairSets n a b // ¬ twoColPairGood p} ≃
      TwoColPairSets n (a + 1) (b - 1) := by
  classical
  refine
    { toFun := badPairToShifted
      invFun := shiftedToBad hba hb
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    rcases p with ⟨⟨⟨A, hA⟩, ⟨B, hB⟩⟩, hbad⟩
    let hc := crossings_nonempty_of_not_dominates A B hbad
    let t := firstCross B A hc
    have hqcard := tailSwapPair_card A B hA hB t (firstCross_prefix_eq_succ B A hc)
    have hqcross : (crossings (tailSwapPair A B t).1 (tailSwapPair A B t).2).Nonempty := by
      apply crossings_nonempty_of_card_gt
      have hC := hqcard.1
      have hD := hqcard.2
      omega
    have hfirst : firstCross (tailSwapPair A B t).1 (tailSwapPair A B t).2 hqcross = t := by
      apply tailSwap_firstCross_eq A B t (firstCross_prefix_eq_succ B A hc)
        (fun u hu => no_cross_before_first B A hc hu)
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      dsimp [badPairToShifted, shiftedToBad]
      rw [hfirst]
      exact congrArg Prod.fst (tailSwapPair_involutive A B t)
    · apply Subtype.ext
      dsimp [badPairToShifted, shiftedToBad]
      rw [hfirst]
      exact congrArg Prod.snd (tailSwapPair_involutive A B t)
  · intro q
    let C := q.1.1
    let D := q.2.1
    have hcard : D.card < C.card := by
      change q.2.1.card < q.1.1.card
      rw [q.2.2, q.1.2]
      omega
    have hc : (crossings C D).Nonempty := crossings_nonempty_of_card_gt C D hcard
    let t := firstCross C D hc
    have hcross := firstCross_prefix_eq_succ C D hc
    have hqcard := tailSwapPair_card_reverse C D q.1.2 q.2.2 t
      hcross
    have hcrosses :
        (crossings (tailSwapPair D C t).1 (tailSwapPair D C t).2).Nonempty := by
      refine ⟨t, ?_⟩
      simp only [crossings, Finset.mem_filter, Finset.mem_univ, true_and]
      change (leftPart (leftPart C t ∪ rightPart D t) t).card >
        (leftPart (leftPart D t ∪ rightPart C t) t).card
      rw [leftPart_leftUnionRight, leftPart_leftUnionRight]
      change prefixSize C t > prefixSize D t
      change prefixSize C t = prefixSize D t + 1 at hcross
      omega
    have hfirst :
        firstCross (tailSwapPair D C t).1 (tailSwapPair D C t).2 hcrosses = t := by
      apply tailSwap_firstCross_eq D C t (firstCross_prefix_eq_succ C D hc)
        (fun u hu => no_cross_before_first C D hc hu)
    have hfirstComp : firstCross (tailSwapPair C D t).2 (tailSwapPair C D t).1
        (by simpa [tailSwapPair] using hcrosses) = t := by
      simpa [tailSwapPair] using hfirst
    apply Prod.ext
    · apply Subtype.ext
      dsimp [badPairToShifted, shiftedToBad]
      rw [hfirstComp]
      exact congrArg Prod.fst (tailSwapPair_involutive C D t)
    · apply Subtype.ext
      dsimp [badPairToShifted, shiftedToBad]
      rw [hfirstComp]
      exact congrArg Prod.snd (tailSwapPair_involutive C D t)

private theorem badPairToShifted_weight {n a b : ℕ}
    (p : {p : TwoColPairSets n a b // ¬ twoColPairGood p}) :
    twoColPairWeight n a b p.1 =
      twoColPairWeight n (a + 1) (b - 1) (badPairToShifted p) := by
  classical
  simp only [twoColPairWeight, badPairToShifted]
  exact tailSwapPair_weight p.1.1.1 p.1.2.1
    (firstCross p.1.2.1 p.1.1.1
      (crossings_nonempty_of_not_dominates p.1.1.1 p.1.2.1 p.2))

private noncomputable def allPairSum (n a b : ℕ) : MvPolynomial (Fin n) ℤ :=
  ∑ p : TwoColPairSets n a b, twoColPairWeight n a b p

private theorem allPairSum_split (n a b : ℕ) :
    allPairSum n a b =
      (∑ p ∈ Finset.univ.filter (twoColPairGood (n := n) (a := a) (b := b)),
        twoColPairWeight n a b p) +
      ∑ p ∈ Finset.univ.filter (fun p => ¬ twoColPairGood p),
        twoColPairWeight n a b p := by
  classical
  simpa [allPairSum, Finset.sum_filter] using
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (twoColPairGood (n := n) (a := a) (b := b))
      (twoColPairWeight n a b)).symm

private theorem esymm_mul_esymm_eq_allPairSum (n a b : ℕ) :
    esymm (Fin n) ℤ a * esymm (Fin n) ℤ b = allPairSum n a b := by
  classical
  simp only [MvPolynomial.esymm_eq_sum_subtype, allPairSum]
  rw [Fintype.sum_mul_sum, ← Fintype.sum_prod_type']
  rfl

private theorem badPairSum_eq_shiftedPairSum (n a b : ℕ) (hba : b ≤ a) (hb : 1 ≤ b) :
    (∑ p ∈ Finset.univ.filter (fun p : TwoColPairSets n a b => ¬ twoColPairGood p),
      twoColPairWeight n a b p) = allPairSum n (a + 1) (b - 1) := by
  classical
  rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  unfold allPairSum
  refine Fintype.sum_equiv (badPairTailSwapEquiv hba hb)
    (fun p => twoColPairWeight n a b p.1)
    (fun q => twoColPairWeight n (a + 1) (b - 1) q) ?_
  intro p
  exact badPairToShifted_weight p

/-- Dual Jacobi–Trudi identity for two columns of lengths `a ≥ b ≥ 1`:
`s_λ = e_a e_b - e_{a+1} e_{b-1}`. -/
theorem schur_twoCol (n a b : ℕ) (hba : b ≤ a) (hb : 1 ≤ b) :
    schur (twoCol a b hba) n =
      esymm (Fin n) ℤ a * esymm (Fin n) ℤ b - esymm (Fin n) ℤ (a + 1) * esymm (Fin n) ℤ (b - 1) := by
  classical
  have hsum :
      (∑ p ∈ Finset.univ.filter (twoColPairGood (n := n) (a := a) (b := b)),
        twoColPairWeight n a b p) =
        allPairSum n a b - allPairSum n (a + 1) (b - 1) := by
    rw [allPairSum_split n a b, badPairSum_eq_shiftedPairSum n a b hba hb]
    ring
  rw [schur_eq_goodPairSum n a b hba]
  rw [esymm_mul_esymm_eq_allPairSum n a b]
  rw [esymm_mul_esymm_eq_allPairSum n (a + 1) (b - 1)]
  exact hsum

/-- A single column: `s_{(1^a)} = e_a`. -/
theorem schur_twoCol_zero (n a : ℕ) : schur (twoCol a 0 (Nat.zero_le a)) n = esymm (Fin n) ℤ a := by
  classical
  rw [schur_eq_twoColSeqSum]
  calc
    (∑ p ∈ Finset.univ.filter (twoColSeqValid a 0 (Nat.zero_le a)),
        twoColWeight n a 0 p) =
      ∑ f ∈ Finset.univ.filter (fun f : Fin a → Fin n => StrictMono f),
        ∏ i : Fin a, X (f i) := by
      refine Finset.sum_equiv (Equiv.prodUnique (Fin a → Fin n) (Fin 0 → Fin n)) ?_ ?_
      · intro p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.prodUnique_apply]
        change twoColSeqValid a 0 (Nat.zero_le a) p ↔ StrictMono p.1
        unfold twoColSeqValid
        constructor
        · rintro ⟨hA, hB, hAB⟩
          exact hA
        · intro hA
          refine ⟨hA, ?_, ?_⟩
          · intro i j hij
            exact Fin.elim0 i
          · intro i
            exact Fin.elim0 i
      · intro p hp
        simp [twoColWeight]
    _ = esymm (Fin n) ℤ a := strictSeqSum_eq_esymm n a

end Kraw
