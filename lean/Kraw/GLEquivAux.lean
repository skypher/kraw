import Kraw.GLRep
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

namespace Kraw

open exteriorPower
open scoped TensorProduct

/-- Left multiplication by a vector on a fixed exterior power. -/
noncomputable def wedgeLeft (D k : ℕ) (v : Fin D → ℂ) :
    (⋀[ℂ]^k (Fin D → ℂ)) →ₗ[ℂ] (⋀[ℂ]^(k + 1) (Fin D → ℂ)) :=
  exteriorPower.alternatingMapLinearEquiv <|
    (exteriorPower.ιMulti ℂ (k + 1)).curryLeft v

@[simp] theorem wedgeLeft_ιMulti (D k : ℕ) (x : Fin D → ℂ) (v : Fin k → Fin D → ℂ) :
    wedgeLeft D k x (exteriorPower.ιMulti ℂ k v) =
      exteriorPower.ιMulti ℂ (k + 1) (Matrix.vecCons x v) := by
  simp [wedgeLeft]

theorem wedgeLeft_natural (D k : ℕ) (f : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    (x : Fin D → ℂ) (a : ⋀[ℂ]^k (Fin D → ℂ)) :
    exteriorPower.map (k + 1) f (wedgeLeft D k x a) =
      wedgeLeft D k (f x) (exteriorPower.map k f a) := by
  have h :
      (exteriorPower.map (k + 1) f).comp (wedgeLeft D k x) =
        (wedgeLeft D k (f x)).comp (exteriorPower.map k f) := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [wedgeLeft]
    rw [show Matrix.vecTail (f ∘ Matrix.vecCons x v) = f ∘ v by
      funext i
      rfl]
  exact LinearMap.congr_fun h a

theorem wedgeLeft_add (D k : ℕ) (x y : Fin D → ℂ) :
    wedgeLeft D k (x + y) = wedgeLeft D k x + wedgeLeft D k y := by
  apply exteriorPower.linearMap_ext
  ext v
  simp [wedgeLeft, Fin.cons, Function.update]

theorem wedgeLeft_smul (D k : ℕ) (c : ℂ) (x : Fin D → ℂ) :
    wedgeLeft D k (c • x) = c • wedgeLeft D k x := by
  apply exteriorPower.linearMap_ext
  ext v
  simp [wedgeLeft, Fin.cons, Function.update]

abbrev transferTarget (D k : ℕ) :=
  (⋀[ℂ]^(k + 2) (Fin D → ℂ)) ⊗[ℂ] (⋀[ℂ]^k (Fin D → ℂ))

attribute [local instance 50] TensorProduct.addCommMonoid

private noncomputable def transferTailAlt (D k : ℕ) (x : Fin D → ℂ)
    (a : ⋀[ℂ]^(k + 1) (Fin D → ℂ)) : (Fin D → ℂ) [⋀^Fin k]→ₗ[ℂ] transferTarget D k :=
  (TensorProduct.mk ℂ _ _ (wedgeLeft D (k + 1) x a)).compAlternatingMap
    (exteriorPower.ιMulti ℂ k)

private noncomputable def transferSlotAltLinear (D k : ℕ)
    (a : ⋀[ℂ]^(k + 1) (Fin D → ℂ)) :
    (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ) [⋀^Fin k]→ₗ[ℂ] transferTarget D k where
  toFun x := transferTailAlt D k x a
  map_add' x y := by
    apply AlternatingMap.ext
    intro v
    simp [transferTailAlt, wedgeLeft_add, TensorProduct.add_tmul]
  map_smul' c x := by
    apply AlternatingMap.ext
    intro v
    simp [transferTailAlt, wedgeLeft_smul, ← TensorProduct.smul_tmul']

private noncomputable def transferSlotLinear (D k : ℕ) :
    (⋀[ℂ]^(k + 1) (Fin D → ℂ)) →ₗ[ℂ]
      (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ) [⋀^Fin k]→ₗ[ℂ] transferTarget D k where
  toFun := transferSlotAltLinear D k
  map_add' a b := by
    apply LinearMap.ext
    intro x
    apply AlternatingMap.ext
    intro v
    simp [transferSlotAltLinear, transferTailAlt, TensorProduct.add_tmul]
  map_smul' c a := by
    apply LinearMap.ext
    intro x
    apply AlternatingMap.ext
    intro v
    simp [transferSlotAltLinear, transferTailAlt, ← TensorProduct.smul_tmul']

private noncomputable def transferAltLinear (D k : ℕ) :
    (⋀[ℂ]^(k + 1) (Fin D → ℂ)) →ₗ[ℂ]
      (⋀[ℂ]^(k + 1) (Fin D → ℂ)) →ₗ[ℂ] transferTarget D k := by
  let e : ((Fin D → ℂ) [⋀^Fin (k + 1)]→ₗ[ℂ] transferTarget D k) ≃ₗ[ℂ]
      (⋀[ℂ]^(k + 1) (Fin D → ℂ)) →ₗ[ℂ] transferTarget D k :=
    @exteriorPower.alternatingMapLinearEquiv ℂ inferInstance (k + 1) (Fin D → ℂ)
      (transferTarget D k) inferInstance inferInstance TensorProduct.addCommGroup inferInstance
  let altify : ((Fin D → ℂ) →ₗ[ℂ]
      (Fin D → ℂ) [⋀^Fin k]→ₗ[ℂ] transferTarget D k) →ₗ[ℂ]
      (Fin D → ℂ) [⋀^Fin (k + 1)]→ₗ[ℂ] transferTarget D k :=
    AlternatingMap.alternatizeUncurryFinLM (R := ℂ) (M := Fin D → ℂ)
      (N := transferTarget D k) (n := k)
  exact e.toLinearMap.comp (altify.comp (transferSlotLinear D k))

noncomputable def transferIntrinsic (D k : ℕ) :
    ((⋀[ℂ]^(k + 1) (Fin D → ℂ)) ⊗[ℂ] (⋀[ℂ]^(k + 1) (Fin D → ℂ))) →ₗ[ℂ]
      transferTarget D k :=
  TensorProduct.lift (transferAltLinear D k)

private theorem transferAltLinear_apply_ιMulti (D k : ℕ)
    (a : ⋀[ℂ]^(k + 1) (Fin D → ℂ)) (v : Fin (k + 1) → Fin D → ℂ) :
    transferAltLinear D k a (exteriorPower.ιMulti ℂ (k + 1) v) =
      ∑ i : Fin (k + 1), ((-1 : ℤ) ^ (i : ℕ)) •
        (wedgeLeft D (k + 1) (v i) a ⊗ₜ[ℂ]
          exteriorPower.ιMulti ℂ k (i.removeNth v)) := by
  simp [transferAltLinear, transferSlotLinear, transferSlotAltLinear, transferTailAlt,
    AlternatingMap.alternatizeUncurryFin_apply]

private theorem transferAltLinear_natural (D k : ℕ)
    (f : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    (v : Fin (k + 1) → Fin D → ℂ) (a : ⋀[ℂ]^(k + 1) (Fin D → ℂ)) :
    transferAltLinear D k (exteriorPower.map (k + 1) f a)
        (exteriorPower.ιMulti ℂ (k + 1) (f ∘ v)) =
      TensorProduct.map (exteriorPower.map (k + 2) f) (exteriorPower.map k f)
        (transferAltLinear D k a (exteriorPower.ιMulti ℂ (k + 1) v)) := by
  rw [transferAltLinear_apply_ιMulti, transferAltLinear_apply_ιMulti]
  simp only [TensorProduct.map_tmul, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  have htail : i.removeNth (f ∘ v) = f ∘ i.removeNth v := by
    funext j
    rfl
  simp [htail, wedgeLeft_natural, exteriorPower.map_apply_ιMulti]

theorem transferIntrinsic_natural (D k : ℕ)
    (f : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) :
    TensorProduct.map (exteriorPower.map (k + 2) f) (exteriorPower.map k f) ∘ₗ
        transferIntrinsic D k =
      transferIntrinsic D k ∘ₗ
        TensorProduct.map (exteriorPower.map (k + 1) f) (exteriorPower.map (k + 1) f) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul,
    transferIntrinsic]
  have h : (TensorProduct.map (exteriorPower.map (k + 2) f) (exteriorPower.map k f)) ∘ₗ
      transferAltLinear D k a =
      (transferAltLinear D k (exteriorPower.map (k + 1) f a)).comp
        (exteriorPower.map (k + 1) f) := by
    letI : AddCommGroup (transferTarget D k) := TensorProduct.addCommGroup
    letI : Module ℂ (transferTarget D k) := TensorProduct.instModule
    exact exteriorPower.linearMap_ext
      (f := (TensorProduct.map (exteriorPower.map (k + 2) f) (exteriorPower.map k f)) ∘ₗ
        transferAltLinear D k a)
      (g := (transferAltLinear D k (exteriorPower.map (k + 1) f a)).comp
        (exteriorPower.map (k + 1) f)) (by
      exact AlternatingMap.ext (R := ℂ) (ι := Fin (k + 1))
        (M := Fin D → ℂ) (N := transferTarget D k)
        (f := ((TensorProduct.map (exteriorPower.map (k + 2) f) (exteriorPower.map k f)) ∘ₗ
          transferAltLinear D k a).compAlternatingMap
            (exteriorPower.ιMulti ℂ (k + 1)))
        (f' := ((transferAltLinear D k (exteriorPower.map (k + 1) f a)).comp
          (exteriorPower.map (k + 1) f)).compAlternatingMap
            (exteriorPower.ιMulti ℂ (k + 1))) (by
          intro v
          change TensorProduct.map (exteriorPower.map (k + 2) f) (exteriorPower.map k f)
              (transferAltLinear D k a (exteriorPower.ιMulti ℂ (k + 1) v)) =
            transferAltLinear D k (exteriorPower.map (k + 1) f a)
              (exteriorPower.map (k + 1) f (exteriorPower.ιMulti ℂ (k + 1) v))
          rw [exteriorPower.map_apply_ιMulti]
          exact (transferAltLinear_natural D k f v a).symm))
  exact DFunLike.congr_fun h b

private noncomputable def subsetVec (D n : ℕ) (A : Set.powersetCard (Fin D) n) :
    Fin n → Fin D → ℂ :=
  Pi.basisFun ℂ (Fin D) ∘ A.1.orderEmbOfFin (Set.powersetCard.mem_iff.mp A.2)

private theorem coordinateWedgeBasis_ιMulti (D n : ℕ)
    (A : Set.powersetCard (Fin D) n) :
    coordinateWedgeBasis D n A = exteriorPower.ιMulti ℂ n (subsetVec D n A) := by
  simp [coordinateWedgeBasis, exteriorPower.basis_apply,
    subsetVec, exteriorPower.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply]

private theorem subsetVec_removeNth (D k : ℕ)
    (B : Set.powersetCard (Fin D) (k + 1)) (p : Fin (k + 1)) :
    p.removeNth (subsetVec D (k + 1) B) =
      subsetVec D k (eraseCoordinate B (B.1.orderEmbOfFin B.2 p)
        (Finset.orderEmbOfFin_mem B.1 B.2 p)) := by
  classical
  let j := B.1.orderEmbOfFin (Set.powersetCard.mem_iff.mp B.2) p
  let hj : j ∈ B.1 := Finset.orderEmbOfFin_mem B.1 (Set.powersetCard.mem_iff.mp B.2) p
  let C := eraseCoordinate B j hj
  have hCcard : (B.1.erase j).card = k := by
    rw [Finset.card_erase_of_mem hj, Set.powersetCard.mem_iff.mp B.2]
    simp
  have hmem (t : Fin k) :
      B.1.orderEmbOfFin (Set.powersetCard.mem_iff.mp B.2) (p.succAbove t) ∈ B.1.erase j := by
    rw [Finset.mem_erase]
    constructor
    · intro h
      apply Fin.succAbove_ne p t
      exact (B.1.orderEmbOfFin (Set.powersetCard.mem_iff.mp B.2)).injective
        (by simpa [j] using h)
    · exact Finset.orderEmbOfFin_mem B.1 (Set.powersetCard.mem_iff.mp B.2) (p.succAbove t)
  have hemb := Finset.orderEmbOfFin_unique hCcard hmem
      ((B.1.orderEmbOfFin (Set.powersetCard.mem_iff.mp B.2)).strictMono.comp
        (Fin.strictMono_succAbove p))
  funext t
  change Pi.basisFun ℂ (Fin D)
      (B.1.orderEmbOfFin (Set.powersetCard.mem_iff.mp B.2) (p.succAbove t)) =
    Pi.basisFun ℂ (Fin D)
      ((B.1.erase (B.1.orderEmbOfFin (Set.powersetCard.mem_iff.mp B.2) p)).orderEmbOfFin
        hCcard t)
  rw [← hemb]

private theorem wedgeLeft_insert_basis (D k : ℕ)
    (A : Set.powersetCard (Fin D) k) (j : Fin D) (hj : j ∉ A.1)
    (C : Set.powersetCard (Fin D) (k + 1)) (p : Fin (k + 1))
    (hp : C.1.orderEmbOfFin (Set.powersetCard.mem_iff.mp C.2) p = j)
    (hrem : p.removeNth (subsetVec D (k + 1) C) = subsetVec D k A) :
    (-1 : ℤ) ^ (p : ℕ) • coordinateWedgeBasis D (k + 1) C =
      wedgeLeft D k (Pi.basisFun ℂ (Fin D) j) (coordinateWedgeBasis D k A) := by
  have hvec : p.insertNth (Pi.basisFun ℂ (Fin D) j) (subsetVec D k A) =
      subsetVec D (k + 1) C := by
    have hpv : subsetVec D (k + 1) C p = Pi.basisFun ℂ (Fin D) j := by
      change Pi.basisFun ℂ (Fin D)
        (C.1.orderEmbOfFin (Set.powersetCard.mem_iff.mp C.2) p) = _
      rw [hp]
    rw [← hrem, ← hpv]
    exact Fin.insertNth_self_removeNth p (subsetVec D (k + 1) C)
  have h := AlternatingMap.neg_one_pow_smul_map_insertNth
    (exteriorPower.ιMulti ℂ (k + 1)) p (Pi.basisFun ℂ (Fin D) j) (subsetVec D k A)
  rw [coordinateWedgeBasis_ιMulti, coordinateWedgeBasis_ιMulti, wedgeLeft_ιMulti, ← hvec]
  exact h

private theorem subsetPositionCard (D n : ℕ)
    (A : Set.powersetCard (Fin D) n) (p : Fin n) :
    (A.1.filter (fun j => j < A.1.orderEmbOfFin
      (Set.powersetCard.mem_iff.mp A.2) p)).card = p.val := by
  classical
  let e := A.1.orderEmbOfFin (Set.powersetCard.mem_iff.mp A.2)
  have himage : (Finset.univ.filter (fun i : Fin n => i < p)).image e =
      A.1.filter (fun j => j < e p) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem A.1 (Set.powersetCard.mem_iff.mp A.2) i,
        e.lt_iff_lt.mpr hi⟩
    · rintro ⟨hx, hxlt⟩
      let i := (A.1.orderIsoOfFin (Set.powersetCard.mem_iff.mp A.2)).symm ⟨x, hx⟩
      have hi_eq : e i = x := by
        change (A.1.orderIsoOfFin (Set.powersetCard.mem_iff.mp A.2) i).val = x
        exact congrArg Subtype.val ((A.1.orderIsoOfFin
          (Set.powersetCard.mem_iff.mp A.2)).apply_symm_apply ⟨x, hx⟩)
      refine ⟨i, ?_, hi_eq⟩
      · apply e.lt_iff_lt.mp
        rw [hi_eq]
        exact hxlt
  rw [← himage, Finset.card_image_of_injective _ e.injective]
  have hIio : Finset.univ.filter (fun i : Fin n => i < p) = Finset.Iio p := by
    ext i
    simp
  rw [hIio, Fin.card_Iio]

private theorem sum_orderEmb {D n : ℕ} {M : Type*} [AddCommMonoid M]
    (A : Set.powersetCard (Fin D) n) (f : Fin D → M) :
    (∑ p : Fin n, f (A.1.orderEmbOfFin (Set.powersetCard.mem_iff.mp A.2) p)) =
      ∑ j ∈ A.1, f j := by
  classical
  let e := A.1.orderEmbOfFin (Set.powersetCard.mem_iff.mp A.2)
  refine Finset.sum_bij (s := Finset.univ) (t := A.1)
    (f := fun p => f (e p)) (g := f) (fun p _ => e p) ?_ ?_ ?_ ?_
  · intro p hp
    exact Finset.orderEmbOfFin_mem A.1 (Set.powersetCard.mem_iff.mp A.2) p
  · intro p hp q hq heq
    exact e.injective heq
  · intro j hj
    let p := (A.1.orderIsoOfFin (Set.powersetCard.mem_iff.mp A.2)).symm ⟨j, hj⟩
    refine ⟨p, Finset.mem_univ _, ?_⟩
    change (A.1.orderIsoOfFin (Set.powersetCard.mem_iff.mp A.2) p).val = j
    exact congrArg Subtype.val ((A.1.orderIsoOfFin
      (Set.powersetCard.mem_iff.mp A.2)).apply_symm_apply ⟨j, hj⟩)
  · intro p hp
    rfl

private theorem wedgeLeft_basis_mem (D n : ℕ)
    (A : Set.powersetCard (Fin D) n) (j : Fin D) (hj : j ∈ A.1) :
    wedgeLeft D n (Pi.basisFun ℂ (Fin D) j) (coordinateWedgeBasis D n A) = 0 := by
  classical
  let q := (A.1.orderIsoOfFin (Set.powersetCard.mem_iff.mp A.2)).symm ⟨j, hj⟩
  have hq : subsetVec D n A q = Pi.basisFun ℂ (Fin D) j := by
    change Pi.basisFun ℂ (Fin D)
      (A.1.orderEmbOfFin (Set.powersetCard.mem_iff.mp A.2) q) = _
    congr 1
    change (A.1.orderIsoOfFin (Set.powersetCard.mem_iff.mp A.2) q).val = j
    exact congrArg Subtype.val ((A.1.orderIsoOfFin
      (Set.powersetCard.mem_iff.mp A.2)).apply_symm_apply ⟨j, hj⟩)
  have hdup : Matrix.vecCons (Pi.basisFun ℂ (Fin D) j) (subsetVec D n A) 0 =
      Matrix.vecCons (Pi.basisFun ℂ (Fin D) j) (subsetVec D n A) q.succ := by
    simp [Matrix.vecCons, hq]
  have hzero := (exteriorPower.ιMulti ℂ (n + 1)).map_eq_zero_of_eq
    (Matrix.vecCons (Pi.basisFun ℂ (Fin D) j) (subsetVec D n A)) hdup
    ((Fin.succ_ne_zero q).symm)
  rw [coordinateWedgeBasis_ιMulti, wedgeLeft_ιMulti]
  exact hzero

theorem transferMap_eq_transferIntrinsic (D k : ℕ) :
    transferMap D (k + 1) = transferIntrinsic D k := by
  apply (coordinateTensorBasis D (k + 1) (k + 1)).ext
  intro AB
  change transferMap D (k + 1)
      ((coordinateTensorBasis D (k + 1) (k + 1)) AB) =
    transferIntrinsic D k ((coordinateTensorBasis D (k + 1) (k + 1)) AB)
  rw [transferMap, Module.Basis.constr_basis]
  rw [transferIntrinsic, coordinateTensorBasis, Module.Basis.tensorProduct_apply',
    TensorProduct.lift.tmul]
  rw [coordinateWedgeBasis_ιMulti, coordinateWedgeBasis_ιMulti]
  rw [transferAltLinear_apply_ιMulti]
  classical
  let A := AB.1
  let B := AB.2
  let e := B.1.orderEmbOfFin (Set.powersetCard.mem_iff.mp B.2)
  let val (j : Fin D) (hA : j ∉ A.1) (hB : j ∈ B.1) : transferTarget D k :=
    (wedgePositionSign A.1 j * wedgePositionSign B.1 j) •
      (coordinateWedgeBasis D (k + 1 + 1) (insertCoordinate A j hA) ⊗ₜ[ℂ]
        coordinateWedgeBasis D (k + 1 - 1) (eraseCoordinate B j hB))
  let g (j : Fin D) : transferTarget D k :=
    if hB : j ∈ B.1 then if hA : j ∉ A.1 then val j hA hB else 0 else 0
  change (∑ j : Fin D, if hA : j ∉ A.1 then
      if hB : j ∈ B.1 then val j hA hB else 0 else 0) =
    ∑ p : Fin (k + 1), (-1 : ℤ) ^ (p : ℕ) •
      (wedgeLeft D (k + 1) (subsetVec D (k + 1) B p)
          (exteriorPower.ιMulti ℂ (k + 1) (subsetVec D (k + 1) A)) ⊗ₜ[ℂ]
        exteriorPower.ιMulti ℂ k (p.removeNth (subsetVec D (k + 1) B)))
  have hswap (j : Fin D) :
      (if hA : j ∉ A.1 then if hB : j ∈ B.1 then val j hA hB else 0 else 0) = g j := by
    dsimp [g]
    by_cases hA : j ∉ A.1 <;> by_cases hB : j ∈ B.1 <;> simp [hA, hB]
  have hterm (p : Fin (k + 1)) : g (e p) =
      (-1 : ℤ) ^ (p : ℕ) •
        (wedgeLeft D (k + 1) (subsetVec D (k + 1) B p)
            (exteriorPower.ιMulti ℂ (k + 1) (subsetVec D (k + 1) A)) ⊗ₜ[ℂ]
          exteriorPower.ιMulti ℂ k (p.removeNth (subsetVec D (k + 1) B))) := by
    let j := e p
    have hjB : j ∈ B.1 := by
      exact Finset.orderEmbOfFin_mem B.1 (Set.powersetCard.mem_iff.mp B.2) p
    have hfirst : subsetVec D (k + 1) B p = Pi.basisFun ℂ (Fin D) j := by
      change Pi.basisFun ℂ (Fin D) (e p) = _
      rfl
    dsimp [g]
    rw [dif_pos hjB]
    by_cases hA : j ∉ A.1
    · rw [dif_pos hA]
      let C := insertCoordinate A j hA
      have hjC : j ∈ C.1 := by simp [C, insertCoordinate]
      have hCcard : C.1.card = (k + 1) + 1 :=
        Set.powersetCard.mem_iff.mp C.2
      let q : Fin ((k + 1) + 1) :=
        (C.1.orderIsoOfFin hCcard).symm ⟨j, hjC⟩
      have hjC' : C.1.orderEmbOfFin hCcard q = j := by
        change (C.1.orderIsoOfFin hCcard q).val = j
        exact congrArg Subtype.val ((C.1.orderIsoOfFin hCcard).apply_symm_apply ⟨j, hjC⟩)
      have herase : eraseCoordinate C j hjC = A := by
        apply Subtype.ext
        change (insert j A.1).erase j = A.1
        exact Finset.erase_insert hA
      have hremRaw := subsetVec_removeNth D (k + 1) C q
      have hrem : q.removeNth (subsetVec D ((k + 1) + 1) C) = subsetVec D (k + 1) A := by
        simpa only [hjC', herase] using hremRaw
      have hw := (wedgeLeft_insert_basis D (k + 1) A j hA C q hjC' hrem).symm
      have hsecond : exteriorPower.ιMulti ℂ k
          (p.removeNth (subsetVec D (k + 1) B)) =
          coordinateWedgeBasis D k (eraseCoordinate B j hjB) := by
        calc
          _ = exteriorPower.ιMulti ℂ k
              (subsetVec D k (eraseCoordinate B j hjB)) := by
                congr 1
                simpa [j, e] using subsetVec_removeNth D k B p
          _ = _ := (coordinateWedgeBasis_ιMulti D k _).symm
      have hposB : (B.1.filter (fun x => x < j)).card = p.val := by
        simpa [j, e] using subsetPositionCard D (k + 1) B p
      have hposC : (C.1.filter (fun x => x < j)).card = q.val := by
        have h := subsetPositionCard D ((k + 1) + 1) C q
        rw [hjC'] at h
        exact h
      have hposA : (A.1.filter (fun x => x < j)).card = q.val := by
        have hfilter : (insert j A.1).filter (fun x => x < j) =
            A.1.filter (fun x => x < j) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hx | hx, hlt⟩
            · subst x
              exact (lt_irrefl _ hlt).elim
            · exact ⟨hx, hlt⟩
          · rintro ⟨hx, hlt⟩
            exact ⟨Or.inr hx, hlt⟩
        simpa [C, insertCoordinate, hfilter] using hposC
      have hcoef : wedgePositionSign A.1 j * wedgePositionSign B.1 j =
          (((-1 : ℤ) ^ (q : ℕ) : ℤ) : ℂ) *
            (((-1 : ℤ) ^ (p : ℕ) : ℤ) : ℂ) := by
        simp only [wedgePositionSign, hposA, hposB]
        norm_cast
      rw [hfirst, ← coordinateWedgeBasis_ιMulti D (k + 1) A]
      rw [hw, hsecond]
      dsimp [val, C, j]
      rw [hcoef]
      simp [← TensorProduct.smul_tmul', smul_smul, mul_comm]
      norm_cast
    · rw [dif_neg hA]
      have hjA : j ∈ A.1 := by
        by_contra hn
        exact hA hn
      have hzero : wedgeLeft D (k + 1) (subsetVec D (k + 1) B p)
          (exteriorPower.ιMulti ℂ (k + 1) (subsetVec D (k + 1) A)) = 0 := by
        rw [hfirst, ← coordinateWedgeBasis_ιMulti D (k + 1) A]
        exact wedgeLeft_basis_mem D (k + 1) A j hjA
      simp [hzero]
  calc
    (∑ j : Fin D, if hA : j ∉ A.1 then
        if hB : j ∈ B.1 then val j hA hB else 0 else 0) =
      ∑ j : Fin D, g j := by
        congr 1
        funext j
        exact hswap j
    _ = ∑ j ∈ B.1, g j := by
      calc
        (∑ j : Fin D, g j) =
            ∑ j : Fin D, if hB : j ∈ B.1 then g j else 0 := by
              apply Finset.sum_congr rfl
              intro j hj
              dsimp [g]
              split_ifs <;> rfl
        _ = ∑ j ∈ B.1, g j := by simp
    _ = ∑ p : Fin (k + 1), g (e p) := (sum_orderEmb B g).symm
    _ = ∑ p : Fin (k + 1), (-1 : ℤ) ^ (p : ℕ) •
        (wedgeLeft D (k + 1) (subsetVec D (k + 1) B p)
            (exteriorPower.ιMulti ℂ (k + 1) (subsetVec D (k + 1) A)) ⊗ₜ[ℂ]
          exteriorPower.ιMulti ℂ k (p.removeNth (subsetVec D (k + 1) B))) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hterm p

theorem transferMap_natural (D s : ℕ) (hs : 1 ≤ s)
    (f : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) :
    TensorProduct.map (exteriorPower.map (s + 1) f) (exteriorPower.map (s - 1) f) ∘ₗ
        transferMap D s =
      transferMap D s ∘ₗ
        TensorProduct.map (exteriorPower.map s f) (exteriorPower.map s f) := by
  let k := s - 1
  have hk : k + 1 = s := Nat.sub_add_cancel hs
  rw [← hk]
  rw [transferMap_eq_transferIntrinsic D k]
  simpa using transferIntrinsic_natural D k f

end Kraw
