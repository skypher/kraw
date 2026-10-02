import Kraw.GLKernel
import Kraw.GLSurj

/-! The character of `W = ker E` on diagonal matrices, and the case `s = 0`. -/

open MvPolynomial
open exteriorPower
open scoped TensorProduct

namespace Kraw

private theorem trace_surjective_add {V T : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Free ℂ V] [Module.Finite ℂ V] [AddCommGroup T] [Module ℂ T]
    [Module.Free ℂ T] [Module.Finite ℂ T] (q : V →ₗ[ℂ] T) (hq : Function.Surjective q)
    (f : V →ₗ[ℂ] V) (g : T →ₗ[ℂ] T) (hcomm : q.comp f = g.comp q) :
    LinearMap.trace ℂ V f =
      LinearMap.trace ℂ (LinearMap.ker q) (f.restrict (by
        intro x hx
        change q x = 0 at hx
        change q (f x) = 0
        have h := LinearMap.congr_fun hcomm x
        simpa only [LinearMap.comp_apply, hx, map_zero] using h)) +
        LinearMap.trace ℂ T g := by
  classical
  let K := LinearMap.ker q
  let hpres : Set.MapsTo f K K := by
    intro x hx
    change q x = 0 at hx
    change q (f x) = 0
    have h := LinearMap.congr_fun hcomm x
    simpa only [LinearMap.comp_apply, hx, map_zero] using h
  let fK := f.restrict hpres
  obtain ⟨i, hi⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)
  let p : V →ₗ[ℂ] K := LinearMap.codRestrict K (LinearMap.id - i.comp q) (by
    intro x
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    have hx : q (i (q x)) = q x := by
      have h := LinearMap.congr_fun hi (q x)
      simpa using h
    rw [map_sub, hx]
    exact sub_self _)
  have hpK : p.comp K.subtype = LinearMap.id := by
    ext x
    change ((LinearMap.id : V →ₗ[ℂ] V) - i.comp q) (x : V) = x
    have hx : q (x : V) = 0 := LinearMap.mem_ker.mp x.2
    simp [LinearMap.sub_apply, LinearMap.comp_apply, hx]
  have hproj : K.subtype.comp p = LinearMap.id - i.comp q := by
    simp [p]
  have hsplit : K.subtype.comp p + i.comp q = LinearMap.id := by
    rw [hproj]
    ext x
    simp [LinearMap.sub_apply, LinearMap.comp_apply, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc]
  have hrestr : f.comp K.subtype = K.subtype.comp fK := by
    ext x
    rfl
  have hdecomp : f = K.subtype.comp (p.comp f) + i.comp (g.comp q) := by
    calc
      f = LinearMap.id.comp f := by simp
      _ = (K.subtype.comp p + i.comp q).comp f := by rw [hsplit]
      _ = K.subtype.comp (p.comp f) + i.comp (q.comp f) := by
        simp only [LinearMap.add_comp, LinearMap.comp_assoc]
      _ = K.subtype.comp (p.comp f) + i.comp (g.comp q) := by rw [hcomm]
  have hfirst : (p.comp f).comp K.subtype = fK := by
    rw [LinearMap.comp_assoc, hrestr, ← LinearMap.comp_assoc, hpK, LinearMap.id_comp]
  have hsecond : (g.comp q).comp i = g := by
    simp [LinearMap.comp_assoc, hi]
  calc
    LinearMap.trace ℂ V f =
        LinearMap.trace ℂ V (K.subtype.comp (p.comp f) + i.comp (g.comp q)) :=
          congrArg (LinearMap.trace ℂ V) hdecomp
    _ = LinearMap.trace ℂ V (K.subtype.comp (p.comp f)) +
        LinearMap.trace ℂ V (i.comp (g.comp q)) := by rw [map_add]
    _ = LinearMap.trace ℂ K ((p.comp f).comp K.subtype) +
        LinearMap.trace ℂ T ((g.comp q).comp i) := by
          rw [LinearMap.trace_comp_comm' (p.comp f) K.subtype,
            LinearMap.trace_comp_comm' (g.comp q) i]
    _ = LinearMap.trace ℂ K fK + LinearMap.trace ℂ T g := by rw [hfirst, hsecond]

private theorem exteriorPowerRep_diag_basis (D k : ℕ) (t : Fin D → ℂˣ)
    (A : Set.powersetCard (Fin D) k) :
    exteriorPowerRep D k (diagGL t) (coordinateWedgeBasis D k A) =
      (∏ i ∈ A.1, (t i : ℂ)) • coordinateWedgeBasis D k A := by
  classical
  let e : Fin k ↪o Fin D := Set.powersetCard.ofFinEmbEquiv.symm A
  have hstd (i : Fin D) :
      standardRep D (diagGL t) (Pi.basisFun ℂ (Fin D) i) =
        (t i : ℂ) • Pi.basisFun ℂ (Fin D) i := by
    ext j
    simp [standardRep, diagGL, Matrix.toLin'_apply, Pi.basisFun_apply,
      Pi.single_apply, Matrix.diagonal_apply, Matrix.mulVec_single_one, smul_eq_mul]
  simp only [exteriorPowerRep, MonoidHom.coe_mk, OneHom.coe_mk,
    coordinateWedgeBasis, exteriorPower.basis_apply]
  rw [exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family,
    exteriorPower.ιMulti_family]
  have hvec :
      (standardRep D (diagGL t) ∘ Pi.basisFun ℂ (Fin D)) ∘ e =
        fun j => (t (e j) : ℂ) • Pi.basisFun ℂ (Fin D) (e j) := by
    funext j
    exact hstd (e j)
  rw [hvec, AlternatingMap.map_smul_univ]
  have hprod : (∏ j : Fin k, (t (e j) : ℂ)) = ∏ i ∈ A.1, (t i : ℂ) := by
    calc
      (∏ j : Fin k, (t (e j) : ℂ)) =
          (Finset.univ.map e.toEmbedding).prod fun i => (t i : ℂ) := by simp
      _ = A.1.prod fun i => (t i : ℂ) := by
        simpa [e, Set.powersetCard.ofFinEmbEquiv_symm_apply] using
          congrArg (fun S : Finset (Fin D) => S.prod fun i => (t i : ℂ))
            (Finset.map_orderEmbOfFin_univ A.1 A.2)
      _ = ∏ i ∈ A.1, (t i : ℂ) := rfl
  rw [hprod]
  have hfun :
      Pi.basisFun ℂ (Fin D) ∘ Set.powersetCard.ofFinEmbEquiv.symm A =
        fun j => Pi.single (e j) 1 := by
    funext j
    simp [e]
  have hfun' :
      (fun j => Pi.basisFun ℂ (Fin D) (e j)) = fun j => Pi.single (e j) 1 := by
    funext j
    simp
  rw [hfun', hfun]

private theorem trace_exteriorPowerRep_diag (D k : ℕ) (t : Fin D → ℂˣ) :
    LinearMap.trace ℂ _ (exteriorPowerRep D k (diagGL t)) =
      eval (fun i => (t i : ℂ)) (map (Int.castRingHom ℂ) (esymm (Fin D) ℤ k)) := by
  classical
  let b := coordinateWedgeBasis D k
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  simp_rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  simp_rw [b, exteriorPowerRep_diag_basis]
  simp [b, map_smul, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  rw [MvPolynomial.esymm_eq_sum_subtype]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_X]
  let e : Set.powersetCard (Fin D) k ≃ {S : Finset (Fin D) // S.card = k} :=
    (Equiv.refl _).subtypeEquiv fun S => Set.powersetCard.mem_iff
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

private noncomputable def targetActionCoord (D s : ℕ) (g : GL (Fin D) ℂ) :
    (PairIdx D (s + 1) (s - 1) → ℂ) →ₗ[ℂ] (PairIdx D (s + 1) (s - 1) → ℂ) :=
  (pairCoord D (s + 1) (s - 1)).toLinearMap ∘ₗ
    TensorProduct.map (exteriorPowerRep D (s + 1) g) (exteriorPowerRep D (s - 1) g) ∘ₗ
      (pairCoord D (s + 1) (s - 1)).symm.toLinearMap

private theorem transferCoord_surjective (D s : ℕ) (hs : 1 ≤ s) :
    Function.Surjective (transferCoord D s) := by
  intro y
  obtain ⟨x, hx⟩ := transferMap_surjective D s hs
    ((pairCoord D (s + 1) (s - 1)).symm y)
  refine ⟨pairCoord D s s x, ?_⟩
  change pairCoord D (s + 1) (s - 1)
    (transferMap D s ((pairCoord D s s).symm (pairCoord D s s x))) = y
  rw [(pairCoord D s s).symm_apply_apply]
  rw [hx]
  exact (pairCoord D (s + 1) (s - 1)).apply_symm_apply y

private theorem transferCoord_equivariant (D s : ℕ) (hs : 1 ≤ s)
    (g : GL (Fin D) ℂ) :
    (transferCoord D s).comp (bigRep D s g) =
      (targetActionCoord D s g).comp (transferCoord D s) := by
  apply LinearMap.ext
  intro x
  simpa [transferCoord, bigRep, targetActionCoord, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.comp_apply] using
      congrArg (pairCoord D (s + 1) (s - 1))
        (LinearMap.congr_fun (transferMap_equivariant D s hs g)
          ((pairCoord D s s).symm x))

set_option maxHeartbeats 1000000 in
private theorem trace_targetActionCoord_diag (D s : ℕ) (t : Fin D → ℂˣ) :
    LinearMap.trace ℂ _ (targetActionCoord D s (diagGL t)) =
      eval (fun i => (t i : ℂ)) (map (Int.castRingHom ℂ) (esymm (Fin D) ℤ (s + 1))) *
      eval (fun i => (t i : ℂ)) (map (Int.castRingHom ℂ) (esymm (Fin D) ℤ (s - 1))) := by
  change LinearMap.trace ℂ _ ((pairCoord D (s + 1) (s - 1)).conj
      (TensorProduct.map (exteriorPowerRep D (s + 1) (diagGL t))
        (exteriorPowerRep D (s - 1) (diagGL t)))) = _
  calc
    LinearMap.trace ℂ _ ((pairCoord D (s + 1) (s - 1)).conj
        (TensorProduct.map (exteriorPowerRep D (s + 1) (diagGL t))
          (exteriorPowerRep D (s - 1) (diagGL t)))) =
    LinearMap.trace ℂ _
          (TensorProduct.map (exteriorPowerRep D (s + 1) (diagGL t))
            (exteriorPowerRep D (s - 1) (diagGL t))) :=
      LinearMap.trace_conj'
        (R := ℂ)
        (M := (⋀[ℂ]^(s + 1) (Fin D → ℂ)) ⊗[ℂ] (⋀[ℂ]^(s - 1) (Fin D → ℂ)))
        (N := PairIdx D (s + 1) (s - 1) → ℂ)
        (TensorProduct.map (exteriorPowerRep D (s + 1) (diagGL t))
          (exteriorPowerRep D (s - 1) (diagGL t)))
        (pairCoord D (s + 1) (s - 1))
    _ = _ := by
      have h := LinearMap.trace_tensorProduct'
        (exteriorPowerRep D (s + 1) (diagGL t))
        (exteriorPowerRep D (s - 1) (diagGL t))
      rw [trace_exteriorPowerRep_diag, trace_exteriorPowerRep_diag] at h
      exact h

set_option maxHeartbeats 1000000 in
private theorem trace_bigRep_diag (D s : ℕ) (t : Fin D → ℂˣ) :
    LinearMap.trace ℂ _ (bigRep D s (diagGL t)) =
      eval (fun i => (t i : ℂ)) (map (Int.castRingHom ℂ) (esymm (Fin D) ℤ s)) *
      eval (fun i => (t i : ℂ)) (map (Int.castRingHom ℂ) (esymm (Fin D) ℤ s)) := by
  change LinearMap.trace ℂ _ ((pairCoord D s s).conj (exteriorTensorRep D s (diagGL t))) = _
  calc
    LinearMap.trace ℂ _ ((pairCoord D s s).conj (exteriorTensorRep D s (diagGL t))) =
        LinearMap.trace ℂ (exteriorTensor D s) (exteriorTensorRep D s (diagGL t)) :=
      LinearMap.trace_conj' (R := ℂ) (M := exteriorTensor D s)
        (N := PairIdx D s s → ℂ) (exteriorTensorRep D s (diagGL t)) (pairCoord D s s)
    _ = LinearMap.trace ℂ (⋀[ℂ]^s (Fin D → ℂ))
          (exteriorPowerRep D s (diagGL t)) *
        LinearMap.trace ℂ (⋀[ℂ]^s (Fin D → ℂ))
          (exteriorPowerRep D s (diagGL t)) := by
      change LinearMap.trace ℂ _
          (TensorProduct.map (exteriorPowerRep D s (diagGL t))
            (exteriorPowerRep D s (diagGL t))) = _
      exact LinearMap.trace_tensorProduct' _ _
    _ = _ := by rw [trace_exteriorPowerRep_diag]

private theorem exteriorPowerRep_zero (D : ℕ) (g : GL (Fin D) ℂ) :
    exteriorPowerRep D 0 g = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply (exteriorPower.zeroEquiv ℂ (Fin D → ℂ)).injective
  have h := congrArg (fun F : (⋀[ℂ]^0 (Fin D → ℂ)) →ₗ[ℂ] ℂ => F x)
    (exteriorPower.zeroEquiv_naturality (standardRep D g))
  simpa [exteriorPowerRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.comp_apply] using h

set_option maxHeartbeats 1000000 in
private theorem trace_bigRep_zero_aux (D : ℕ) (g : GL (Fin D) ℂ) :
    LinearMap.trace ℂ _ (bigRep D 0 g) = 1 := by
  have hdim : Module.finrank ℂ (⋀[ℂ]^0 (Fin D → ℂ)) = 1 := by
    rw [(exteriorPower.zeroEquiv ℂ (Fin D → ℂ)).finrank_eq]
    simp
  calc
    LinearMap.trace ℂ _ (bigRep D 0 g) =
        LinearMap.trace ℂ (exteriorTensor D 0) (exteriorTensorRep D 0 g) := by
      change LinearMap.trace ℂ _
        ((pairCoord D 0 0).conj (exteriorTensorRep D 0 g)) = _
      exact LinearMap.trace_conj' (R := ℂ) (M := exteriorTensor D 0)
        (N := PairIdx D 0 0 → ℂ) (exteriorTensorRep D 0 g) (pairCoord D 0 0)
    _ = LinearMap.trace ℂ _
          (TensorProduct.map (exteriorPowerRep D 0 g) (exteriorPowerRep D 0 g)) := rfl
    _ = LinearMap.trace ℂ (⋀[ℂ]^0 (Fin D → ℂ)) (exteriorPowerRep D 0 g) *
        LinearMap.trace ℂ (⋀[ℂ]^0 (Fin D → ℂ)) (exteriorPowerRep D 0 g) :=
      LinearMap.trace_tensorProduct' _ _
    _ = 1 := by rw [exteriorPowerRep_zero, LinearMap.trace_id, hdim]; norm_num

/-- `trace_W(diag t) = e_s(t)² - e_{s+1}(t) e_{s-1}(t)`. -/
theorem trace_kerRep_diag (D s : ℕ) (hs : 1 ≤ s) (t : Fin D → ℂˣ) :
    LinearMap.trace ℂ _ (kerRep D s hs (diagGL t)) =
      eval (fun i => (t i : ℂ)) (map (Int.castRingHom ℂ)
        (esymm (Fin D) ℤ s * esymm (Fin D) ℤ s - esymm (Fin D) ℤ (s + 1) * esymm (Fin D) ℤ (s - 1))) := by
  let q := transferCoord D s
  let f := bigRep D s (diagGL t)
  let g := targetActionCoord D s (diagGL t)
  have hsum := trace_surjective_add q (transferCoord_surjective D s hs) f g
    (transferCoord_equivariant D s hs (diagGL t))
  rw [trace_bigRep_diag, trace_targetActionCoord_diag] at hsum
  have hpres : Set.MapsTo f (LinearMap.ker q) (LinearMap.ker q) := by
    intro x hx
    change q x = 0 at hx
    change q (f x) = 0
    have h := LinearMap.congr_fun (transferCoord_equivariant D s hs (diagGL t)) x
    change q (f x) = g (q x) at h
    simpa [hx] using h
  change LinearMap.trace ℂ (LinearMap.ker q) (f.restrict hpres) = _
  simp only [map_sub, map_mul, eval_sub, eval_mul]
  exact (eq_sub_iff_add_eq).2 hsum.symm

/-- For `s = 0` the tensor square `Λ^0 ⊗ Λ^0` is the trivial one-dimensional representation. -/
theorem trace_bigRep_zero (D : ℕ) (g : GL (Fin D) ℂ) :
    LinearMap.trace ℂ _ (bigRep D 0 g) = 1 := by
  exact trace_bigRep_zero_aux D g

end Kraw
