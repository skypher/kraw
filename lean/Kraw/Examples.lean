import Kraw.Main
import Kraw.SeqDefs

/-!
# The example `(M,Q) = (5,2)` and the real-argument counterexample (paper §1.1)
-/

namespace Kraw

open Polynomial

private theorem p_5_2_0 : p 5 2 0 = 1 := p_zero 5 2

private theorem p_5_2_1 : p 5 2 1 = 3 := by
  simpa using p_one 5 2

private theorem p_5_2_2 : p 5 2 2 = 1 := by
  have h := p_rec (M := 5) (Q := 2) 1
  norm_num at h
  rw [p_5_2_0, p_5_2_1] at h
  norm_num at h
  omega

private theorem p_5_2_3 : p 5 2 3 = -5 := by
  have h := p_rec (M := 5) (Q := 2) 2
  norm_num at h
  rw [p_5_2_1, p_5_2_2] at h
  norm_num at h
  omega

private theorem p_5_2_4 : p 5 2 4 = -5 := by
  have h := p_rec (M := 5) (Q := 2) 3
  norm_num at h
  rw [p_5_2_2, p_5_2_3] at h
  norm_num at h
  omega

private theorem p_5_2_5 : p 5 2 5 = 1 := by
  have h := p_rec (M := 5) (Q := 2) 4
  norm_num at h
  rw [p_5_2_3, p_5_2_4] at h
  norm_num at h
  omega

private theorem p_5_2_6 : p 5 2 6 = 3 := by
  have h := p_rec (M := 5) (Q := 2) 5
  norm_num at h
  rw [p_5_2_4, p_5_2_5] at h
  norm_num at h
  omega

private theorem p_5_2_7 : p 5 2 7 = 1 := by
  have h := p_rec (M := 5) (Q := 2) 6
  norm_num at h
  rw [p_5_2_5, p_5_2_6] at h
  norm_num at h
  omega

/-- §1.1: `(p_s)_{s=0}^7 = (1,3,1,-5,-5,1,3,1)` for `(M,Q) = (5,2)`. -/
theorem example_p : (List.range 8).map (fun s : ℕ => p 5 2 s) = [1, 3, 1, -5, -5, 1, 3, 1] := by
  norm_num [List.range_succ, p_5_2_0, p_5_2_1, p_5_2_2, p_5_2_3,
    p_5_2_4, p_5_2_5, p_5_2_6, p_5_2_7]

/-- §1.1: `(Tur(s))_{s=0}^7 = (1,8,16,30,30,16,8,1)` for `(M,Q) = (5,2)`. -/
theorem example_Tur :
    (List.range 8).map (fun s : ℕ => Tur 5 2 s) = [1, 8, 16, 30, 30, 16, 8, 1] := by
  have hm1 : p 5 2 (-1 : ℤ) = 0 := p_of_neg (M := 5) (Q := 2) (by norm_num)
  have h8 : p 5 2 8 = 0 := p_of_gt (M := 5) (Q := 2) (by norm_num)
  norm_num [List.range_succ, Tur, hm1, h8, p_5_2_0, p_5_2_1, p_5_2_2,
    p_5_2_3, p_5_2_4, p_5_2_5, p_5_2_6, p_5_2_7]

/-- The generalized binomial coefficient `C(a,n) = a(a-1)⋯(a-n+1)/n!`. -/
noncomputable def gbinom (a : ℝ) (n : ℕ) : ℝ := (descPochhammer ℝ n).eval a / (n.factorial : ℝ)

/-- The formal power series `(1+w)^a`. -/
noncomputable def binomSeries (a : ℝ) : PowerSeries ℝ := PowerSeries.mk (gbinom a)

/-- `[w^s] (1+w)^{D-q} (1-w)^q` for real `q` (and `0` for `s < 0`). -/
noncomputable def pReal (D : ℕ) (q : ℝ) (s : ℤ) : ℝ :=
  if s < 0 then 0 else
    PowerSeries.coeff s.toNat
      (binomSeries ((D : ℝ) - q) * PowerSeries.rescale (-1 : ℝ) (binomSeries q))

private theorem gbinom_natCast (n k : ℕ) :
    gbinom (n : ℝ) k = (Nat.choose n k : ℝ) := by
  unfold gbinom
  exact (Nat.cast_choose_eq_descPochhammer_div (K := ℝ) n k).symm

private theorem binomSeries_natCast (n : ℕ) :
    binomSeries (n : ℝ) = (1 + PowerSeries.X) ^ n := by
  ext k
  have hright : (1 + PowerSeries.X : PowerSeries ℝ) ^ n =
      (((1 + X : ℝ[X]) ^ n : ℝ[X]) : PowerSeries ℝ) := by simp
  rw [hright, binomSeries, PowerSeries.coeff_mk, Polynomial.coeff_coe,
    Polynomial.coeff_one_add_X_pow, gbinom_natCast]

private theorem rescale_binomSeries_natCast (n : ℕ) :
    PowerSeries.rescale (-1 : ℝ) (binomSeries (n : ℝ)) =
      (1 - PowerSeries.X) ^ n := by
  rw [binomSeries_natCast]
  have hbase : PowerSeries.rescale (-1 : ℝ) (1 + PowerSeries.X) =
      1 - PowerSeries.X := by
    rw [map_add, map_one, PowerSeries.rescale_neg_one_X]
    ring
  calc
    PowerSeries.rescale (-1 : ℝ) ((1 + PowerSeries.X) ^ n) =
        (PowerSeries.rescale (-1 : ℝ) (1 + PowerSeries.X)) ^ n := map_pow _ _ _
    _ = (1 - PowerSeries.X) ^ n := by rw [hbase]

private theorem pReal_coeff_antidiagonal (D : ℕ) (q : ℝ) (s : ℤ) (hs : 0 ≤ s) :
    pReal D q s =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal s.toNat,
        gbinom ((D : ℝ) - q) ij.1 * ((-1 : ℝ) ^ ij.2 * gbinom q ij.2) := by
  simp [pReal, hs, binomSeries, PowerSeries.coeff_mul, PowerSeries.coeff_rescale,
    PowerSeries.coeff_mk]

private theorem sum_nat_antidiagonal (n : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, f ij) =
      ∑ i ∈ Finset.range (n + 1), f (i, n - i) := by
  rw [Finset.Nat.antidiagonal_eq_map]
  simp only [Finset.sum_map]
  rfl

/-- For an integer argument `q = Q ≤ D`, the series coefficients are the `p_s`. -/
theorem pReal_natCast (D Q : ℕ) (hQ : Q ≤ D) (s : ℤ) :
    pReal D Q s = (p (D - Q) Q s : ℝ) := by
  by_cases hs : s < 0
  · simp [pReal, hs, p_of_neg (M := D - Q) (Q := Q) hs]
  · have hs0 : 0 ≤ s := le_of_not_gt hs
    have harg : (D : ℝ) - (Q : ℝ) = ((D - Q : ℕ) : ℝ) := by
      exact (Nat.cast_sub hQ).symm
    have hmap :
        (gen (D - Q) Q).map (Int.castRingHom ℝ) =
          (1 + X : ℝ[X]) ^ (D - Q) * (1 - X) ^ Q := by
      simp [gen]
    have hmapSeries :
        (((gen (D - Q) Q).map (Int.castRingHom ℝ)) : PowerSeries ℝ) =
          (1 + PowerSeries.X) ^ (D - Q) * (1 - PowerSeries.X) ^ Q := by
      simpa [Polynomial.coe_mul, Polynomial.coe_pow] using
        congrArg (fun f : ℝ[X] => (f : PowerSeries ℝ)) hmap
    have hseries :
        binomSeries ((D : ℝ) - (Q : ℝ)) *
            PowerSeries.rescale (-1 : ℝ) (binomSeries (Q : ℝ)) =
          (((gen (D - Q) Q).map (Int.castRingHom ℝ)) : PowerSeries ℝ) := by
      rw [harg, binomSeries_natCast, rescale_binomSeries_natCast]
      exact hmapSeries.symm
    have hcoeff := congrArg (PowerSeries.coeff s.toNat) hseries
    rw [Polynomial.coeff_coe, Polynomial.coeff_map] at hcoeff
    simpa [pReal, p, hs] using hcoeff

/-- §1.1: at `(D, q, s) = (4, 8/7, 2)` the real relaxation gives `T_2 = -1430/117649 < 0`. -/
theorem real_relaxation_counterexample : stepSeq (pReal 4 (8 / 7)) 2 = -1430 / 117649 := by
  have h1 : pReal 4 (8 / 7) 1 = 12 / 7 := by
    rw [pReal_coeff_antidiagonal 4 (8 / 7) 1 (by norm_num)]
    rw [show (1 : ℤ).toNat = 1 by
      exact_mod_cast (Int.toNat_of_nonneg (by norm_num : 0 ≤ (1 : ℤ)))]
    rw [sum_nat_antidiagonal]
    norm_num [Finset.sum_range_succ, gbinom, descPochhammer_eval_eq_prod_range]
  have h2 : pReal 4 (8 / 7) 2 = -26 / 49 := by
    rw [pReal_coeff_antidiagonal 4 (8 / 7) 2 (by norm_num)]
    rw [show (2 : ℤ).toNat = 2 by
      exact_mod_cast (Int.toNat_of_nonneg (by norm_num : 0 ≤ (2 : ℤ)))]
    rw [sum_nat_antidiagonal]
    norm_num [Finset.sum_range_succ, gbinom, descPochhammer_eval_eq_prod_range]
  have h3 : pReal 4 (8 / 7) 3 = -692 / 343 := by
    rw [pReal_coeff_antidiagonal 4 (8 / 7) 3 (by norm_num)]
    rw [show (3 : ℤ).toNat = 3 by
      exact_mod_cast (Int.toNat_of_nonneg (by norm_num : 0 ≤ (3 : ℤ)))]
    rw [sum_nat_antidiagonal]
    norm_num [Finset.sum_range_succ, gbinom, descPochhammer_eval_eq_prod_range]
  have h4 : pReal 4 (8 / 7) 4 = -1439 / 2401 := by
    rw [pReal_coeff_antidiagonal 4 (8 / 7) 4 (by norm_num)]
    rw [show (4 : ℤ).toNat = 4 by
      exact_mod_cast (Int.toNat_of_nonneg (by norm_num : 0 ≤ (4 : ℤ)))]
    rw [sum_nat_antidiagonal]
    norm_num [Finset.sum_range_succ, gbinom, descPochhammer_eval_eq_prod_range]
  norm_num [stepSeq, turSeq, h1, h2, h3, h4]

end Kraw
