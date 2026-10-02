import Kraw.QuadForm
import Kraw.GapStrip

/-!
# Gap cells with even `Q`

Paper Theorem 4.1 (tangent comparison), valid for every gap offset `u ≥ 1`.
-/

namespace Kraw

variable (M Q : ℕ)

private noncomputable def evenQdev (M Q : ℕ) (j : ℤ) : ℤ :=
  ((M : ℤ) + Q + 2) * p M Q (j + 1) - ((M : ℤ) - Q) * p M Q j

private noncomputable def evenQratio (M Q : ℕ) (j : ℤ) : ℝ :=
  -((evenQdev M Q j : ℝ) / (p M Q j : ℝ))

private noncomputable def evenQLambda (M Q : ℕ) : ℝ :=
  (((M : ℝ) + Q + 2) ^ 2 - ((M : ℝ) - Q) ^ 2)

private noncomputable def evenQtheta (M Q : ℕ) : ℝ :=
  Real.arctan (Real.sqrt (evenQLambda M Q) / ((M : ℝ) - Q))

private noncomputable def evenQangle (M Q : ℕ) (j : ℤ) : ℝ :=
  (((2 * j - ((M : ℤ) + Q) : ℤ) : ℝ) * evenQtheta M Q) / 2

private theorem evenQ_step_identity (j : ℤ) :
    (j + 2) * ((M : ℤ) + Q + 1 - j) * T M Q j =
      (2 * (j + 1) - ((M : ℤ) + Q)) * ((M : ℤ) + Q + 1 - j) * Tur M Q j -
        p M Q (j + 1) *
          (((M : ℤ) + Q + 2) * p M Q (j + 1) - ((M : ℤ) - Q) * p M Q j) := by
  have hr₀ := p_rec M Q j
  have hr₁ :
      (j + 2) * p M Q (j + 2) =
        ((M : ℤ) - Q) * p M Q (j + 1) + (j - ((M : ℤ) + Q)) * p M Q j := by
    simpa only [show j + 1 + 1 = j + 2 by omega,
      show j + 1 - 1 = j by omega] using p_rec M Q (j + 1)
  unfold T Tur
  simp only [show j + 1 - 1 = j by omega,
    show j + 1 + 1 = j + 2 by omega]
  linear_combination (((M : ℤ) + Q + 1 - j) * p M Q j) * hr₁ -
    (((M : ℤ) + Q - j) * p M Q (j + 1)) * hr₀

private theorem evenQ_tur_identity (j : ℤ) :
    (((M : ℤ) + Q + 1 - j) * Tur M Q j) =
      ((M : ℤ) + Q + 1 - j) * p M Q j ^ 2 -
        ((M : ℤ) - Q) * p M Q j * p M Q (j + 1) +
          (j + 1) * p M Q (j + 1) ^ 2 := by
  have hr := p_rec M Q j
  unfold Tur
  linear_combination -(p M Q (j + 1)) * hr

private theorem evenQ_pd_recurrence (j : ℤ) :
    (j + 2) * ((M : ℤ) + Q + 2) *
        (((M : ℤ) + Q + 2) * p M Q (j + 2) - ((M : ℤ) - Q) * p M Q (j + 1)) =
      (((M : ℤ) + Q - j) *
        (((M : ℤ) - Q) * (((M : ℤ) + Q + 2) * p M Q (j + 1) -
              ((M : ℤ) - Q) * p M Q j) -
          (((M : ℤ) + Q + 2) ^ 2 - ((M : ℤ) - Q) ^ 2) * p M Q j)) := by
  have hr :
      (j + 2) * p M Q (j + 2) =
        ((M : ℤ) - Q) * p M Q (j + 1) + (j - ((M : ℤ) + Q)) * p M Q j := by
    simpa only [show j + 1 + 1 = j + 2 by omega,
      show j + 1 - 1 = j by omega] using p_rec M Q (j + 1)
  linear_combination (((M : ℤ) + Q + 2) ^ 2) * hr

private theorem evenQ_dev_recurrence (j : ℤ) :
    (j + 2) * ((M : ℤ) + Q + 2) * evenQdev M Q (j + 1) =
      (((M : ℤ) + Q - j) *
        (((M : ℤ) - Q) * evenQdev M Q j -
          (((M : ℤ) + Q + 2) ^ 2 - ((M : ℤ) - Q) ^ 2) * p M Q j)) := by
  simpa [evenQdev, show j + 1 + 1 = j + 2 by omega] using
    evenQ_pd_recurrence M Q j

private theorem evenQ_arctan_add_scaled {x L z : ℝ} (hx : 0 < x) (hL : 0 < L)
    (hzx : z < x) :
    Real.arctan (z / Real.sqrt L) + Real.arctan (Real.sqrt L / x) =
      Real.arctan (((L + x * z) / (x - z)) / Real.sqrt L) := by
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hprod : (z / Real.sqrt L) * (Real.sqrt L / x) < 1 := by
    calc
      (z / Real.sqrt L) * (Real.sqrt L / x) = z / x := by
        field_simp
      _ < 1 := (div_lt_one₀ hx).2 hzx
  have hratio :
      (z / Real.sqrt L + Real.sqrt L / x) /
          (1 - (z / Real.sqrt L) * (Real.sqrt L / x)) =
        ((L + x * z) / (x - z)) / Real.sqrt L := by
    have hsquare : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
    have hxdiff : x - z ≠ 0 := (sub_pos.mpr hzx).ne'
    field_simp [hsqrt.ne', hx.ne', hxdiff]
    rw [hsquare]
    ring
  rw [Real.arctan_add hprod, hratio]

private theorem evenQ_F_tan {x L z : ℝ} (hx : 0 < x) (hL : 0 < L)
    (hzx : z < x) :
    (L + x * z) / (x - z) =
      Real.sqrt L * Real.tan (Real.arctan (z / Real.sqrt L) +
        Real.arctan (Real.sqrt L / x)) := by
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  calc
    (L + x * z) / (x - z) =
        Real.sqrt L * (((L + x * z) / (x - z)) / Real.sqrt L) := by
          field_simp
    _ = Real.sqrt L * Real.tan
        (Real.arctan (((L + x * z) / (x - z)) / Real.sqrt L)) := by
          rw [Real.tan_arctan]
    _ = Real.sqrt L * Real.tan
        (Real.arctan (z / Real.sqrt L) + Real.arctan (Real.sqrt L / x)) := by
          rw [← evenQ_arctan_add_scaled hx hL hzx]

private noncomputable def evenQF (x L z : ℝ) : ℝ := (L + x * z) / (x - z)

private theorem evenQF_pos {x L z : ℝ} (hx : 0 < x) (hL : 0 < L)
    (hz : 0 ≤ z) (hzx : z < x) : 0 < evenQF x L z := by
  unfold evenQF
  have hnum : 0 < L + x * z := by
    have hmul := mul_nonneg (le_of_lt hx) hz
    linarith
  exact div_pos hnum (sub_pos.mpr hzx)

private theorem evenQ_bound_lt_x {x L a : ℝ} (hx : 0 < x) (hL : 0 < L)
    (ha : 0 ≤ a) (hθ : 0 < Real.arctan (Real.sqrt L / x))
    (haθ : a + Real.arctan (Real.sqrt L / x) < Real.pi / 2) :
    Real.sqrt L * Real.tan a < x := by
  have hcomp : 0 < Real.pi / 2 - Real.arctan (Real.sqrt L / x) := by linarith
  have hcompTop : Real.pi / 2 - Real.arctan (Real.sqrt L / x) < Real.pi / 2 := by
    linarith
  have htan := Real.tan_lt_tan_of_lt_of_lt_pi_div_two (x := a)
    (y := Real.pi / 2 - Real.arctan (Real.sqrt L / x))
    (by linarith [Real.pi_pos]) hcompTop (by linarith)
  have hcompTan : Real.tan (Real.pi / 2 - Real.arctan (Real.sqrt L / x)) =
      x / Real.sqrt L := by
    rw [Real.tan_pi_div_two_sub, Real.tan_arctan]
    field_simp [Real.sqrt_ne_zero'.2 hL]
  have hsqrt : Real.sqrt L ≠ 0 := (Real.sqrt_pos.2 hL).ne'
  calc
    Real.sqrt L * Real.tan a <
        Real.sqrt L * Real.tan (Real.pi / 2 - Real.arctan (Real.sqrt L / x)) :=
      mul_lt_mul_of_pos_left htan (Real.sqrt_pos.2 hL)
    _ = Real.sqrt L * (x / Real.sqrt L) := by rw [hcompTan]
    _ = x := by field_simp [hsqrt]

private theorem evenQF_tangent_bound {x L z a : ℝ} (hx : 0 < x) (hL : 0 < L)
    (hz : 0 ≤ z) (hzx : z < x) (hza : z ≤ Real.sqrt L * Real.tan a)
    (ha : 0 ≤ a) (haθ : a + Real.arctan (Real.sqrt L / x) < Real.pi / 2) :
    evenQF x L z ≤ Real.sqrt L *
      Real.tan (a + Real.arctan (Real.sqrt L / x)) := by
  have hθ : 0 < Real.arctan (Real.sqrt L / x) := by
    apply Real.arctan_pos.2
    positivity
  let β := Real.arctan (z / Real.sqrt L)
  have hβa : β ≤ a := by
    have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
    have hza' : z ≤ Real.tan a * Real.sqrt L := by simpa [mul_comm] using hza
    have hdiv : z / Real.sqrt L ≤ Real.tan a := (div_le_iff₀ hsqrt).2 hza'
    have hmono := Real.arctan_mono hdiv
    have haTop : a < Real.pi / 2 := by linarith [hθ, haθ]
    have htan := Real.arctan_tan (by linarith [Real.pi_pos]) haTop
    dsimp [β]
    simpa [htan] using hmono
  have hsum : β + Real.arctan (Real.sqrt L / x) =
      Real.arctan (evenQF x L z / Real.sqrt L) := by
    dsimp [β, evenQF]
    exact evenQ_arctan_add_scaled hx hL hzx
  have hβmem : β + Real.arctan (Real.sqrt L / x) ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [hsum]
    exact Real.arctan_mem_Ioo _
  have hamem : a + Real.arctan (Real.sqrt L / x) ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [ha, hθ, haθ, Real.pi_pos]
  have htanle := Real.strictMonoOn_tan.monotoneOn hβmem hamem
    (add_le_add hβa le_rfl)
  unfold evenQF
  rw [evenQ_F_tan hx hL hzx]
  exact mul_le_mul_of_nonneg_left htanle (Real.sqrt_nonneg L)

private theorem evenQ_half_tan {a x L : ℝ} (hx : 0 < x) (ha : 0 < a)
    (hL : 0 < L) (hLid : L = a ^ 2 - x ^ 2) :
    Real.sqrt L * Real.tan (Real.arctan (Real.sqrt L / x) / 2) = a - x := by
  have hsqrtpos : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsqrtsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
  have hden : 0 < a + x := by positivity
  have hgap : 0 < (a + x) ^ 2 - L := by rw [hLid]; nlinarith
  have hrootlt : Real.sqrt L < a + x := by
    apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (le_of_lt hden)).1
    nlinarith [hsqrtsq, hgap]
  let y : ℝ := Real.sqrt L / (a + x)
  have hypos : 0 < y := by dsimp [y]; positivity
  have hylt : y < 1 := by
    dsimp [y]
    exact (div_lt_one₀ hden).2 hrootlt
  have hdeny : 1 - y ^ 2 ≠ 0 := by
    have hysq : y ^ 2 < 1 := by nlinarith [hypos, hylt]
    exact (sub_pos.mpr hysq).ne'
  have harg : 2 * y / (1 - y ^ 2) = Real.sqrt L / x := by
    have hLid' := hLid
    have hdenSq : (a + x) ^ 2 - Real.sqrt L ^ 2 ≠ 0 := by
      nlinarith [hsqrtsq, hgap]
    dsimp [y]
    field_simp [hden.ne', hx.ne', hdeny, hdenSq]
    nlinarith [hsqrtsq, hLid']
  have hdouble := Real.two_mul_arctan (by linarith [hypos]) hylt
  rw [harg] at hdouble
  calc
    Real.sqrt L * Real.tan (Real.arctan (Real.sqrt L / x) / 2) =
        Real.sqrt L * Real.tan ((2 * Real.arctan y) / 2) := by rw [← hdouble]
    _ = Real.sqrt L * Real.tan (Real.arctan y) := by congr 1 <;> ring_nf
    _ = Real.sqrt L * y := by rw [Real.tan_arctan]
    _ = a - x := by
      dsimp [y]
      have hfactor : L = (a - x) * (a + x) := by rw [hLid]; ring
      field_simp [hden.ne']
      nlinarith [hsqrtsq, hfactor]

private theorem evenQ_angle_bound {u : ℤ} {θ : ℝ} (hu : 1 ≤ u)
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hsmall : ((u : ℝ) + 1) ^ 2 * (Real.sin θ) ^ 2 < 7 / 3) :
    ((u : ℝ) + 2) * θ / 2 < Real.pi / 2 := by
  by_cases hu1 : u = 1
  · subst u
    have hsinpos : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
    have hsinrefpos : 0 < Real.sin (Real.pi / 3) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    have hsinSq : (Real.sin θ) ^ 2 < 3 / 4 := by nlinarith [hsmall]
    have hsinlt : Real.sin θ < Real.sin (Real.pi / 3) := by
      apply (sq_lt_sq₀ hsinpos.le hsinrefpos.le).1
      rw [Real.sq_sin_pi_div_three]
      exact hsinSq
    have hθmem : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have hπmem : Real.pi / 3 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have hθlt : θ < Real.pi / 3 :=
      (Real.strictMonoOn_sin.lt_iff_lt hθmem hπmem).1 hsinlt
    nlinarith [Real.pi_pos]
  · by_cases hu2 : u = 2
    · subst u
      have hsinpos : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
      have hsinrefpos : 0 < Real.sin (Real.pi / 4) :=
        Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
      have hsinSq : (Real.sin θ) ^ 2 < 1 / 2 := by nlinarith [hsmall]
      have hsinrefSq : (Real.sin (Real.pi / 4)) ^ 2 = 1 / 2 := by
        rw [Real.sin_pi_div_four]
        have hroot : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        nlinarith [hroot]
      have hsinlt : Real.sin θ < Real.sin (Real.pi / 4) := by
        apply (sq_lt_sq₀ hsinpos.le hsinrefpos.le).1
        rw [hsinrefSq]
        exact hsinSq
      have hθmem : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_pos]
      have hπmem : Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_pos]
      have hθlt : θ < Real.pi / 4 :=
        (Real.strictMonoOn_sin.lt_iff_lt hθmem hπmem).1 hsinlt
      nlinarith [Real.pi_pos]
    · have hu3 : 3 ≤ u := by omega
      have huR : 3 ≤ (u : ℝ) := by exact_mod_cast hu3
      have hsinpos : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
      let y : ℝ := ((u : ℝ) + 1) * Real.sin θ
      let z : ℝ := ((u : ℝ) + 2) * Real.sin θ
      have hypos : 0 < y := by dsimp [y]; positivity
      have hySq : y ^ 2 < 7 / 3 := by
        dsimp [y]
        nlinarith [hsmall]
      have hratio : 4 * ((u : ℝ) + 2) ≤ 5 * ((u : ℝ) + 1) := by
        nlinarith [huR]
      have hzy : z ≤ (5 / 4) * y := by
        have hmul := mul_le_mul_of_nonneg_right hratio (le_of_lt hsinpos)
        dsimp [y, z]
        nlinarith [hmul]
      have hzpos : 0 ≤ z := by dsimp [z]; positivity
      have hzSq : z ^ 2 < 4 := by
        have hpow := mul_self_le_mul_self hzpos hzy
        nlinarith [hySq, hpow]
      have hJordan := Real.mul_le_sin (le_of_lt hθ0) (le_of_lt hθpi)
      have hscaled : ((u : ℝ) + 2) * θ / 2 ≤ Real.pi / 4 * z := by
        have hmul := mul_le_mul_of_nonneg_right hJordan
          (show 0 ≤ Real.pi * ((u : ℝ) + 2) / 4 by positivity)
        have hleft : ((u : ℝ) + 2) * θ / 2 =
            (2 / Real.pi * θ) * (Real.pi * ((u : ℝ) + 2) / 4) := by
          field_simp [ne_of_gt Real.pi_pos]
          ring
        have hright : Real.pi / 4 * z =
            Real.sin θ * (Real.pi * ((u : ℝ) + 2) / 4) := by
          dsimp [z]
          ring
        rw [hleft, hright]
        exact hmul
      have hlast : Real.pi / 4 * z < Real.pi / 2 := by
        nlinarith [Real.pi_pos, hzSq]
      exact lt_of_le_of_lt hscaled hlast

private theorem evenQ_strip_product {m q d U : ℝ} (hm : 0 ≤ m) (hq : 0 ≤ q)
    (hd : d = m + q)
    (hstrip : 6 * (2 * q + 3) * U < 7 * (d + 3)) :
    U * (4 * (q + 1) * (m + 1) / (d + 2) ^ 2) < 7 / 3 := by
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have hd3 : 0 < d + 3 := by linarith
  have hdenU : 0 < 6 * (2 * q + 3) := by positivity
  have hstrip' : U * (6 * (2 * q + 3)) < 7 * (d + 3) := by
    calc
      U * (6 * (2 * q + 3)) = 6 * (2 * q + 3) * U := by ring
      _ < 7 * (d + 3) := hstrip
  have hUbnd : U < 7 * (d + 3) / (6 * (2 * q + 3)) :=
    (lt_div_iff₀ hdenU).2 hstrip'
  have hqden : 0 < 2 * q + 3 := by positivity
  let qrat : ℝ := (q + 1) / (2 * q + 3)
  have hqratpos : 0 < qrat := by dsimp [qrat]; positivity
  have hqratle : qrat ≤ 1 / 2 := by
    apply (div_le_iff₀ hqden).2
    nlinarith
  have hdden : 0 < (d + 2) ^ 2 := by positivity
  let mrat : ℝ := (m + 1) * (d + 3) / (d + 2) ^ 2
  have hdiff : (d + 2) ^ 2 - (m + 1) * (d + 3) = q * (d + 3) + 1 := by
    rw [hd]
    ring
  have hmrlt : mrat < 1 := by
    apply (div_lt_one₀ hdden).2
    nlinarith [hq, hd3]
  have hupperEq :
      7 * (d + 3) / (6 * (2 * q + 3)) *
          (4 * (q + 1) * (m + 1) / (d + 2) ^ 2) =
        (14 / 3) * qrat * mrat := by
    dsimp [qrat, mrat]
    field_simp [hdenU.ne', hqden.ne', hdden.ne']
    ring
  have hApos : 0 < (14 / 3) * qrat := by positivity
  have hAle : (14 / 3) * qrat ≤ 7 / 3 := by nlinarith [hqratle]
  have hAm : (14 / 3) * qrat * mrat < (14 / 3) * qrat := by
    have h := mul_lt_mul_of_pos_left hmrlt hApos
    simpa using h
  have hupperlt :
      7 * (d + 3) / (6 * (2 * q + 3)) *
          (4 * (q + 1) * (m + 1) / (d + 2) ^ 2) < 7 / 3 := by
    rw [hupperEq]
    linarith
  calc
    U * (4 * (q + 1) * (m + 1) / (d + 2) ^ 2) <
        (7 * (d + 3) / (6 * (2 * q + 3))) *
          (4 * (q + 1) * (m + 1) / (d + 2) ^ 2) :=
      mul_lt_mul_of_pos_right hUbnd (by positivity)
    _ < 7 / 3 := hupperlt

set_option maxHeartbeats 1000000
private theorem evenQ_ratio_successor {j : ℤ} {a : ℝ}
    (hx : 0 < (M : ℤ) - Q) (hj0 : 0 ≤ j)
    (hjD : j ≤ (M : ℤ) + Q)
    (hjcenter : (M : ℤ) + Q ≤ 2 * j + 2)
    (hp : p M Q j ≠ 0) (hz : 0 ≤ evenQratio M Q j)
    (ha : 0 ≤ a) (haeq : a = evenQangle M Q j)
    (hza : evenQratio M Q j ≤ Real.sqrt (evenQLambda M Q) * Real.tan a)
    (haθ : a + evenQtheta M Q < Real.pi / 2) :
    p M Q (j + 1) ≠ 0 ∧ 0 ≤ evenQratio M Q (j + 1) ∧
      evenQratio M Q (j + 1) ≤
        Real.sqrt (evenQLambda M Q) * Real.tan (evenQangle M Q (j + 1)) := by
  let D : ℤ := (M : ℤ) + Q
  let x : ℤ := (M : ℤ) - Q
  let Dr : ℝ := (D : ℝ)
  let xr : ℝ := (x : ℝ)
  let L : ℝ := evenQLambda M Q
  let θ : ℝ := evenQtheta M Q
  let z : ℝ := evenQratio M Q j
  let p₀ : ℝ := (p M Q j : ℝ)
  let p₁ : ℝ := (p M Q (j + 1) : ℝ)
  let d₀ : ℝ := (evenQdev M Q j : ℝ)
  let d₁ : ℝ := (evenQdev M Q (j + 1) : ℝ)
  have hLid : L = 4 * ((Q : ℝ) + 1) * ((M : ℝ) + 1) := by
    dsimp [L, evenQLambda]
    push_cast
    ring
  have hL : 0 < L := by rw [hLid]; positivity
  have hxr : 0 < xr := by dsimp [xr, x]; exact_mod_cast hx
  have hD2 : 0 < Dr + 2 := by dsimp [Dr, D]; positivity
  have hJ2 : 0 < (j : ℝ) + 2 := by exact_mod_cast (show 0 < j + 2 by omega)
  have hp₀ : p₀ ≠ 0 := by dsimp [p₀]; exact_mod_cast hp
  have hzdef : z = -d₀ / p₀ := by
    dsimp [z, d₀, p₀, evenQratio]
    rw [← neg_div]
  have hd₀ : d₀ = -z * p₀ := by
    rw [hzdef]
    field_simp [hp₀]
  have hpnrelZ :
      (D + 2) * p M Q (j + 1) = x * p M Q j + evenQdev M Q j := by
    dsimp [D, x, evenQdev]
    ring
  have hpnrel : (Dr + 2) * p₁ = xr * p₀ + d₀ := by
    dsimp [Dr, xr, p₁, p₀, d₀]
    exact_mod_cast hpnrelZ
  have hpnrel' : (Dr + 2) * p₁ = p₀ * (xr - z) := by
    rw [hd₀] at hpnrel
    nlinarith [hpnrel]
  have hθeq : θ = Real.arctan (Real.sqrt L / xr) := by
    dsimp [θ, evenQtheta, L, xr, x]
    rw [Int.cast_sub]
    rfl
  have haθ' : a + Real.arctan (Real.sqrt L / xr) < Real.pi / 2 := by
    rw [← hθeq]
    exact haθ
  have hBlt : Real.sqrt L * Real.tan a < xr := by
    apply evenQ_bound_lt_x hxr hL ha
      (by
        apply Real.arctan_pos.2
        positivity)
      ?_
    exact haθ'
  have hzx : z < xr := lt_of_le_of_lt hza hBlt
  have hzxpos : 0 < xr - z := sub_pos.mpr hzx
  have hp₁ : p₁ ≠ 0 := by
    have hprod : p₀ * (xr - z) ≠ 0 := mul_ne_zero hp₀ hzxpos.ne'
    have hprod' : (Dr + 2) * p₁ ≠ 0 := by simpa [hpnrel'] using hprod
    intro hpzero
    apply hprod'
    simp [p₁, hpzero]
  have hp₁cast : (p M Q (j + 1) : ℝ) ≠ 0 := by
    dsimp [p₁] at hp₁ ⊢
    exact_mod_cast hp₁
  have hrecZ := evenQ_dev_recurrence M Q j
  have hrecCast := congrArg (fun t : ℤ => (t : ℝ)) hrecZ
  have hrec : ((j : ℝ) + 2) * (Dr + 2) * d₁ =
      (Dr - (j : ℝ)) * (xr * d₀ - L * p₀) := by
    dsimp [Dr, D, xr, x, d₁, d₀, p₀, L, evenQLambda]
    push_cast at hrecCast
    simpa [Int.cast_sub, Int.cast_add] using hrecCast
  have hrecMul := congrArg (fun t : ℝ => t * p₁) hrec
  have hpnMul := congrArg (fun t : ℝ => t * (((j : ℝ) + 2) * d₁)) hpnrel'
  rw [hd₀] at hrecMul
  have hcrossMul :
      p₀ * (-(((j : ℝ) + 2) * d₁) * (xr - z)) =
        p₀ * ((Dr - (j : ℝ)) * (L + xr * z) * p₁) := by
    nlinarith [hrecMul, hpnMul]
  have hcross := mul_left_cancel₀ hp₀ hcrossMul
  have hratioEq : evenQratio M Q (j + 1) =
      ((Dr - (j : ℝ)) / ((j : ℝ) + 2)) * evenQF xr L z := by
    change -(d₁ / p₁) =
      ((Dr - (j : ℝ)) / ((j : ℝ) + 2)) * ((L + xr * z) / (xr - z))
    have hJne : (j : ℝ) + 2 ≠ 0 := hJ2.ne'
    field_simp [hp₁, hJne, hzxpos.ne']
    nlinarith [hcross]
  have hjDreal : (j : ℝ) ≤ Dr := by
    dsimp [Dr, D]
    exact_mod_cast hjD
  have hnum : 0 ≤ Dr - (j : ℝ) := by linarith
  have hκ : 0 ≤ (Dr - (j : ℝ)) / ((j : ℝ) + 2) :=
    div_nonneg hnum hJ2.le
  have hκle : (Dr - (j : ℝ)) / ((j : ℝ) + 2) ≤ 1 := by
    apply (div_le_one₀ hJ2).2
    have hcenterReal : Dr ≤ 2 * (j : ℝ) + 2 := by
      dsimp [Dr, D]
      exact_mod_cast hjcenter
    have hnum' : Dr - (j : ℝ) ≤ (j : ℝ) + 2 := by linarith
    linarith
  have hFpos : 0 < evenQF xr L z := evenQF_pos hxr hL hz hzx
  have hFbound : evenQF xr L z ≤
      Real.sqrt L * Real.tan (a + θ) := by
    have hza' : z ≤ Real.sqrt L * Real.tan a := by simpa [z, L] using hza
    have hangle' : a + Real.arctan (Real.sqrt L / xr) < Real.pi / 2 := by
      rw [← hθeq]
      exact haθ
    have hbound := evenQF_tangent_bound hxr hL hz hzx hza' ha hangle'
    rw [← hθeq] at hbound
    exact hbound
  have hnextNonneg : 0 ≤ evenQratio M Q (j + 1) := by
    rw [hratioEq]
    exact mul_nonneg hκ (le_of_lt hFpos)
  have hκF :
      ((Dr - (j : ℝ)) / ((j : ℝ) + 2)) * evenQF xr L z ≤ evenQF xr L z := by
    calc
      _ ≤ 1 * evenQF xr L z := mul_le_mul_of_nonneg_right hκle (le_of_lt hFpos)
      _ = evenQF xr L z := one_mul _
  have hangleNext : evenQangle M Q (j + 1) = a + θ := by
    calc
      evenQangle M Q (j + 1) = evenQangle M Q j + evenQtheta M Q := by
        dsimp [evenQangle]
        push_cast
        ring
      _ = a + θ := by rw [← haeq]
  have hnextBound : evenQratio M Q (j + 1) ≤
      Real.sqrt L * Real.tan (evenQangle M Q (j + 1)) := by
    rw [hratioEq, hangleNext]
    exact hκF.trans hFbound
  exact ⟨by
    intro hzero
    apply hp₁
    have hzeroReal : (p M Q (j + 1) : ℝ) = 0 := by exact_mod_cast hzero
    simpa [p₁] using hzeroReal,
    hnextNonneg,
    by simpa [L] using hnextBound⟩

private theorem evenQ_anchor {u c : ℤ} (hQM : Q ≤ M) (hQ : Even Q)
    (hg : Gap ((M : ℤ) + Q) ((M : ℤ) - Q) u)
    (hc : 2 * c - ((M : ℤ) + Q) = 0 ∨ 2 * c - ((M : ℤ) + Q) = 1) :
    p M Q c ≠ 0 ∧ 0 ≤ evenQratio M Q c ∧
      evenQratio M Q c ≤ Real.sqrt (evenQLambda M Q) * Real.tan (evenQangle M Q c) := by
  let D : ℤ := (M : ℤ) + Q
  let x : ℤ := (M : ℤ) - Q
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hx0 : 0 ≤ x := by dsimp [x]; omega
  have hxD : x ≤ D := by dsimp [x, D]; omega
  have hxpos : 0 < x := by
    dsimp [x]
    exact gap_x_pos hg hD0 hx0
  have hxR : 0 < (x : ℝ) := by exact_mod_cast hxpos
  have hsign : (-1 : ℤ) ^ Q = 1 := by
    obtain ⟨k, hk⟩ := hQ
    have hk' : Q = 2 * k := by omega
    rw [hk']
    rw [pow_mul]
    norm_num
  have hreflect : ∀ j : ℤ, p M Q (D - j) = p M Q j := by
    intro j
    have h := p_refl M Q j
    simpa [D, hsign] using h
  have hLambdaId : evenQLambda M Q =
      4 * ((Q : ℝ) + 1) * ((M : ℝ) + 1) := by
    dsimp [evenQLambda]
    push_cast
    ring
  have hLambda : 0 < evenQLambda M Q := by rw [hLambdaId]; positivity
  rcases hc with heven | hodd
  · have hDform : (M : ℤ) + Q = 2 * c := by omega
    have hc0 : 0 ≤ c := by omega
    have hc1 : 1 ≤ c := by
      have hxD' : 0 < D := lt_of_lt_of_le (by simpa [x] using hxpos) hxD
      omega
    have hprev : p M Q (c - 1) = p M Q (c + 1) := by
      have h := hreflect (c + 1)
      have hi : D - (c + 1) = c - 1 := by dsimp [D]; omega
      simpa [hi] using h
    have hrec := p_rec M Q c
    rw [hprev, hDform] at hrec
    have hdev0 : evenQdev M Q c = 0 := by
      unfold evenQdev
      rw [hDform]
      nlinarith [hrec]
    have hnc := no_consec_zero M Q (j := c) hc0 (by rw [hDform]; omega)
    have hpc : p M Q c ≠ 0 := by
      by_contra hp0
      have hdev : ((M : ℤ) + Q + 2) * p M Q (c + 1) = 0 := by
        simpa [evenQdev, hp0] using hdev0
      have hcoef : (M : ℤ) + Q + 2 ≠ 0 := by omega
      have hnext0 : p M Q (c + 1) = 0 := (mul_eq_zero.mp hdev).resolve_left hcoef
      exact hnc ⟨hp0, hnext0⟩
    have hratio0 : evenQratio M Q c = 0 := by
      unfold evenQratio
      rw [hdev0]
      simp
    have hangle0 : evenQangle M Q c = 0 := by
      unfold evenQangle
      rw [heven]
      simp
    rw [hratio0, hangle0]
    simp [hpc]
  · have hDform : (M : ℤ) + Q = 2 * c - 1 := by omega
    have hc0 : 1 ≤ c := by
      have hxD' : 0 < D := lt_of_lt_of_le (by simpa [x] using hxpos) hxD
      omega
    have hprev : p M Q (c - 1) = p M Q c := by
      have h := hreflect c
      have hi : D - c = c - 1 := by dsimp [D]; omega
      simpa [hi] using h
    have hnc := no_consec_zero M Q (j := c - 1) (by omega) (by omega)
    have hpc : p M Q c ≠ 0 := by
      intro hp0
      have hprev0 : p M Q (c - 1) = 0 := hprev.trans hp0
      exact hnc ⟨hprev0, by simpa using hp0⟩
    have hrec := p_rec M Q c
    rw [hprev, hDform] at hrec
    have hrec' : (c + 1) * p M Q (c + 1) =
        ((M : ℤ) - Q - c) * p M Q c := by nlinarith [hrec]
    have hdevScale : (c + 1) * evenQdev M Q c =
        -c * (D + 2 - x) * p M Q c := by
      unfold evenQdev
      rw [hDform]
      have hdelta : D + 2 - x = 2 * c + 1 - ((M : ℤ) - Q) := by
        dsimp [D]
        rw [hDform]
        omega
      rw [hdelta]
      nlinarith [hrec']
    have hpcR : (p M Q c : ℝ) ≠ 0 := by exact_mod_cast hpc
    let delta : ℝ := ((D + 2 - x : ℤ) : ℝ)
    let kappa : ℝ := (c : ℝ) / ((c : ℝ) + 1)
    have hscaledR : ((c : ℝ) + 1) * (evenQdev M Q c : ℝ) =
        -(c : ℝ) * delta * (p M Q c : ℝ) := by
      dsimp [delta]
      exact_mod_cast hdevScale
    have hratioBase : evenQratio M Q c = kappa * delta := by
      unfold evenQratio
      dsimp [kappa]
      field_simp [hpcR, (show (0 : ℝ) < (c : ℝ) + 1 by positivity).ne']
      nlinarith [hscaledR]
    have hkappa0 : 0 ≤ kappa := by
      dsimp [kappa]
      positivity
    have hkappa1 : kappa ≤ 1 := by
      apply (div_le_one₀ (show 0 < (c : ℝ) + 1 by positivity)).2
      linarith
    have hdeltaEq : D + 2 - x = 2 * Q + 2 := by
      dsimp [D, x]
      ring
    have hdelta : 0 < delta := by
      dsimp [delta]
      rw [hdeltaEq]
      positivity
    have hLid : evenQLambda M Q =
        (((D + 2 : ℤ) : ℝ) ^ 2 - (x : ℝ) ^ 2) := by
      dsimp [evenQLambda, D, x]
      push_cast
      ring
    have hhalf := evenQ_half_tan hxR (by positivity) hLambda hLid
    have hhalf' : Real.sqrt (evenQLambda M Q) *
        Real.tan (evenQtheta M Q / 2) = delta := by
      dsimp [evenQtheta, delta]
      have hxRdef : (x : ℝ) = (M : ℝ) - Q := by
        dsimp [x]
        push_cast
        ring
      rw [← hxRdef]
      simpa only [Int.cast_sub, Int.cast_add] using hhalf
    have hangleBase : evenQangle M Q c = evenQtheta M Q / 2 := by
      unfold evenQangle
      rw [hodd]
      ring
    have hratioNonneg : 0 ≤ kappa * delta := mul_nonneg hkappa0 hdelta.le
    have hratioLe : kappa * delta ≤ delta := by
      calc
        kappa * delta ≤ 1 * delta := mul_le_mul_of_nonneg_right hkappa1 hdelta.le
        _ = delta := one_mul _
    rw [hratioBase, hangleBase, hhalf']
    exact ⟨hpc, hratioNonneg, hratioLe⟩

private theorem evenQ_tur_pos {s : ℤ} (hQM : Q ≤ M)
    (hsD : s ≤ (M : ℤ) + Q)
    (hg : Gap ((M : ℤ) + Q) ((M : ℤ) - Q)
      (2 * s - ((M : ℤ) + Q))) : 0 < Tur M Q s := by
  let D : ℤ := (M : ℤ) + Q
  let x : ℤ := (M : ℤ) - Q
  let u : ℤ := 2 * s - D
  change Gap D x u at hg
  have hsD' : s ≤ D := by simpa [D] using hsD
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hx0 : 0 ≤ x := by dsimp [x]; omega
  have hxD : x ≤ D := by dsimp [x, D]; omega
  have hu : 1 ≤ u := hg.1
  have hflow : (u + 1) ^ 2 < (D + 1) ^ 2 - x ^ 2 := hg.2.2
  have hs0 : 0 ≤ s := by dsimp [u] at hu; omega
  have huSq : u ^ 2 < (u + 1) ^ 2 := by nlinarith [hu]
  have huEq : u = 2 * s - D := by rfl
  have hrSq : (2 * s - D) ^ 2 < (D + 1) ^ 2 - x ^ 2 := by
    rw [← huEq]
    exact huSq.trans hflow
  let A : ℤ := D + 1 - s
  have hA : 0 < A := by dsimp [A]; omega
  have hs1 : 0 < s + 1 := by omega
  have hdisc : x ^ 2 < 4 * A * (s + 1) := by
    have hid : 4 * A * (s + 1) = (D + 2) ^ 2 - (2 * s - D) ^ 2 := by
      dsimp [A]
      ring
    rw [hid]
    nlinarith [hrSq, hD0]
  have hdet : 0 < 4 * A * (s + 1) - x ^ 2 := by linarith
  have hformEq : A * Tur M Q s =
      A * p M Q s ^ 2 - x * p M Q s * p M Q (s + 1) +
        (s + 1) * p M Q (s + 1) ^ 2 := by
    simpa [A, D, x] using evenQ_tur_identity M Q s
  have hcomplete :
      4 * A * (A * p M Q s ^ 2 - x * p M Q s * p M Q (s + 1) +
        (s + 1) * p M Q (s + 1) ^ 2) =
        (2 * A * p M Q s - x * p M Q (s + 1)) ^ 2 +
          (4 * A * (s + 1) - x ^ 2) * p M Q (s + 1) ^ 2 := by
    ring
  have hnc := no_consec_zero M Q hs0 hsD'
  have hpair : p M Q s ≠ 0 ∨ p M Q (s + 1) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hnc ⟨h.1, h.2⟩
  have hsumpos :
      0 < (2 * A * p M Q s - x * p M Q (s + 1)) ^ 2 +
        (4 * A * (s + 1) - x ^ 2) * p M Q (s + 1) ^ 2 := by
    rcases hpair with hp | hnext
    · by_cases hnext0 : p M Q (s + 1) = 0
      · rw [hnext0]
        have hne : 2 * A * p M Q s ≠ 0 := by
          apply mul_ne_zero
          · apply mul_ne_zero <;> norm_num <;> linarith [hA]
          · exact hp
        have hne' : 2 * A * p M Q s - x * 0 ≠ 0 := by simpa using hne
        exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hne') (by positivity)
      · have hsq : 0 < p M Q (s + 1) ^ 2 := sq_pos_of_ne_zero hnext0
        have hterm := mul_pos hdet hsq
        nlinarith
    · have hsq : 0 < p M Q (s + 1) ^ 2 := sq_pos_of_ne_zero hnext
      have hterm := mul_pos hdet hsq
      nlinarith
  have hformpos :
      0 < A * p M Q s ^ 2 - x * p M Q s * p M Q (s + 1) +
        (s + 1) * p M Q (s + 1) ^ 2 := by
    by_contra hnot
    have hformnonpos :
        A * p M Q s ^ 2 - x * p M Q s * p M Q (s + 1) +
          (s + 1) * p M Q (s + 1) ^ 2 ≤ 0 := le_of_not_gt hnot
    have hprodnonpos := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 4 * A)
      hformnonpos
    nlinarith [hcomplete, hsumpos]
  have hATur : 0 < A * Tur M Q s := by rw [hformEq]; exact hformpos
  by_contra hnot
  have hTurNonpos : Tur M Q s ≤ 0 := le_of_not_gt hnot
  have hprodnonpos := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hA) hTurNonpos
  nlinarith

private theorem evenQ_offset_flow {D x u r : ℤ} (hg : Gap D x u)
    (hD : 0 ≤ D) (hx : 0 ≤ x) (hxD : x ≤ D)
    (hr0 : 0 ≤ r) (hru : r ≤ u) : r ^ 2 < (D + 1) ^ 2 - x ^ 2 := by
  by_cases hrpos : 0 < r
  · have hgap := gap_hered hg hD hx hxD (by omega) hru
    have hstep : r ^ 2 < (r + 1) ^ 2 := by nlinarith
    exact hstep.trans hgap.2.2
  · have hrzero : r = 0 := by omega
    subst r
    have hu : 1 ≤ u := hg.1
    have hstep : 0 < (u + 1) ^ 2 := by nlinarith
    linarith [hg.2.2]

/-- Theorem 4.1: if `Q ≤ M` and `Q` is even, every gap cell has `T_s ≥ 0`. -/
theorem T_nonneg_gap_even (hQM : Q ≤ M) (hQ : Even Q) {s : ℤ} (hs : s ≤ (M : ℤ) + Q)
    (hg : Gap ((M : ℤ) + Q) ((M : ℤ) - Q) (2 * s - ((M : ℤ) + Q))) :
    0 ≤ T M Q s := by
  let D : ℤ := (M : ℤ) + Q
  let x : ℤ := (M : ℤ) - Q
  let u : ℤ := 2 * s - D
  change Gap D x u at hg
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hx0 : 0 ≤ x := by dsimp [x]; omega
  have hxD : x ≤ D := by dsimp [x, D]; omega
  have hxpos : 0 < x := gap_x_pos hg hD0 hx0
  have hxR : 0 < (x : ℝ) := by exact_mod_cast hxpos
  have hxRdef : (x : ℝ) = (M : ℝ) - Q := by
    dsimp [x]
    push_cast
    ring
  have hxRreal : 0 < (M : ℝ) - Q := by rw [← hxRdef]; exact hxR
  have hDplus : 0 < (D : ℝ) + 2 := by exact_mod_cast (show 0 < D + 2 by omega)
  have hDplusx : (x : ℝ) < (D : ℝ) + 2 := by
    exact_mod_cast (show x < D + 2 by omega)
  have hDform : D = x + 2 * Q := by dsimp [D, x]; omega
  have hstrip := gap_strip hg (by omega) hx0 hDform
  have hstripR :
      6 * (2 * (Q : ℝ) + 3) * ((u : ℝ) + 1) ^ 2 < 7 * ((D : ℝ) + 3) := by
    exact_mod_cast hstrip
  have hDreal : (D : ℝ) = (M : ℝ) + Q := by
    dsimp [D]
    push_cast
    ring
  have hLambdaId : evenQLambda M Q =
      ((D + 2 : ℤ) : ℝ) ^ 2 - (x : ℝ) ^ 2 := by
    dsimp [evenQLambda, D, x]
    push_cast
    ring
  have hLambdaIdR : evenQLambda M Q =
      ((D : ℝ) + 2) ^ 2 - (x : ℝ) ^ 2 := by
    simpa only [Int.cast_add, Int.cast_ofNat] using hLambdaId
  have hLambdaProdId : evenQLambda M Q =
      4 * ((Q : ℝ) + 1) * ((M : ℝ) + 1) := by
    dsimp [evenQLambda]
    push_cast
    ring
  have hLambda : 0 < evenQLambda M Q := by
    rw [hLambdaIdR]
    have hprod := mul_pos (sub_pos.mpr hDplusx)
      (show 0 < (D : ℝ) + 2 + x by positivity)
    have hfactor : ((D : ℝ) + 2) ^ 2 - (x : ℝ) ^ 2 =
        ((D : ℝ) + 2 - x) * ((D : ℝ) + 2 + x) := by ring
    rw [hfactor]
    exact hprod
  let theta : ℝ := evenQtheta M Q
  have htheta0 : 0 < theta := by
    dsimp [theta, evenQtheta]
    apply Real.arctan_pos.2
    exact div_pos (Real.sqrt_pos.2 hLambda) hxRreal
  have hthetaTop : theta < Real.pi / 2 := by
    dsimp [theta, evenQtheta]
    exact Real.arctan_lt_pi_div_two _
  have hsinsq : (Real.sin theta) ^ 2 =
      evenQLambda M Q / (((D : ℝ) + 2) ^ 2) := by
    dsimp [theta, evenQtheta]
    rw [← hxRdef]
    rw [Real.sin_sq_arctan]
    have hsqrt : Real.sqrt (evenQLambda M Q) ^ 2 = evenQLambda M Q :=
      Real.sq_sqrt hLambda.le
    have hsum : (x : ℝ) ^ 2 + evenQLambda M Q = ((D : ℝ) + 2) ^ 2 := by
      nlinarith [hLambdaIdR]
    have hden : 1 + (Real.sqrt (evenQLambda M Q) / ((M : ℝ) - Q)) ^ 2 ≠ 0 := by
      positivity
    have hsimp :
        (Real.sqrt (evenQLambda M Q) / (x : ℝ)) ^ 2 /
            (1 + (Real.sqrt (evenQLambda M Q) / (x : ℝ)) ^ 2) =
          evenQLambda M Q / ((x : ℝ) ^ 2 + evenQLambda M Q) := by
      field_simp [hxRreal.ne', hden]
      rw [hsqrt]
      ring
    rw [hsimp, ← hsum]
  have hstripProduct := evenQ_strip_product (m := (M : ℝ)) (q := (Q : ℝ))
      (d := (D : ℝ)) (U := ((u : ℝ) + 1) ^ 2)
      (by positivity) (by positivity) hDreal hstripR
  have hstripProduct' : ((u : ℝ) + 1) ^ 2 *
      (evenQLambda M Q / (((D : ℝ) + 2) ^ 2)) < 7 / 3 := by
    rw [← hLambdaProdId] at hstripProduct
    exact hstripProduct
  have hsmall : ((u : ℝ) + 1) ^ 2 * (Real.sin theta) ^ 2 < 7 / 3 := by
    calc
      ((u : ℝ) + 1) ^ 2 * (Real.sin theta) ^ 2 =
          ((u : ℝ) + 1) ^ 2 *
            (evenQLambda M Q / (((D : ℝ) + 2) ^ 2)) := by rw [hsinsq]
      _ < 7 / 3 := hstripProduct'
  have hangleBound := evenQ_angle_bound hg.1 htheta0 hthetaTop hsmall
  have hs0 : 0 ≤ s := by
    have hu1 := hg.1
    dsimp [u, D] at hu1
    omega
  have hsD : s ≤ D := by simpa [D] using hs
  have hu : 1 ≤ u := hg.1
  have hU0 : (u + 1) ^ 2 < (D + 1) ^ 2 - x ^ 2 := hg.2.2
  have hcchoice : 2 * ((D + 1) / 2) - D = 0 ∨
      2 * ((D + 1) / 2) - D = 1 := by omega
  let c : ℤ := (D + 1) / 2
  have hcchoice' : 2 * c - D = 0 ∨ 2 * c - D = 1 := by simpa [c] using hcchoice
  have hcs : c ≤ s := by
    dsimp [c, u] at *
    omega
  have hn0 : 0 ≤ s - c := by omega
  let n : ℕ := (s - c).toNat
  have hncast : (n : ℤ) = s - c := by
    dsimp [n]
    exact Int.toNat_of_nonneg hn0
  have hcn : c + (n : ℤ) = s := by omega
  have hJn : (c + (n : ℤ)) = s := hcn
  let U₀ : ℤ := (D + 1) ^ 2 - x ^ 2
  let J : ℕ → ℤ := fun k => c + (k : ℤ)
  let R : ℕ → ℤ := fun k => 2 * J k - D
  let P : ℕ → Prop := fun k =>
    p M Q (J k) ≠ 0 ∧
      0 ≤ evenQratio M Q (J k) ∧
      evenQratio M Q (J k) ≤
        Real.sqrt (evenQLambda M Q) * Real.tan (evenQangle M Q (J k)) ∧
      R k ^ 2 < U₀
  have hRn : R n = u := by
    dsimp [R, J, u]
    rw [hJn]
  have hRformula (k : ℕ) : R k = (2 * c - D) + 2 * (k : ℤ) := by
    dsimp [R, J]
    ring
  have hRnonneg (k : ℕ) : 0 ≤ R k := by
    have hk0 : 0 ≤ (k : ℤ) := by exact_mod_cast (Nat.zero_le k)
    rw [hRformula]
    rcases hcchoice' with hzero | hone <;> omega
  have hRle (k : ℕ) (hk : k ≤ n) : R k ≤ u := by
    have hkz : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hk
    have hmono : R k ≤ R n := by
      rw [hRformula, hRformula]
      nlinarith [hkz]
    exact hmono.trans_eq hRn
  have hJnonneg (k : ℕ) : 0 ≤ J k := by
    have hr := hRnonneg k
    dsimp [R] at hr
    omega
  have hJle (k : ℕ) (hk : k ≤ n) : J k ≤ s := by
    have hkz : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hk
    calc
      J k ≤ J n := by
        dsimp [J]
        nlinarith [hkz]
      _ = s := hJn
  have hcenterBound (k : ℕ) : D ≤ 2 * J k + 2 := by
    have hr := hRnonneg k
    dsimp [R] at hr
    omega
  have hangleCoord (k : ℕ) : evenQangle M Q (J k) =
      ((R k : ℝ) * theta) / 2 := by
    dsimp [evenQangle, R, J, D, theta]
  have hflowOfR (k : ℕ) (hr0 : 0 ≤ R k) (hru : R k ≤ u) :
      R k ^ 2 < U₀ := by
    exact evenQ_offset_flow hg hD0 hx0 hxD hr0 hru
  have hanchor := evenQ_anchor M Q hQM hQ hg hcchoice'
  rcases hanchor with ⟨hpC, hzC, hzaC⟩
  have hflowC : R 0 ^ 2 < U₀ := hflowOfR 0 (hRnonneg 0) (hRle 0 (by omega))
  have hPzero : P 0 := by
    simpa [P, J, R] using ⟨hpC, hzC, hzaC, hflowC⟩
  have hpath : ∀ k : ℕ, k ≤ n → P k := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => exact hPzero
      | succ m =>
        have hm : m ≤ n := by omega
        have hprev := ih m (by omega) hm
        rcases hprev with ⟨hp, hz, hza, hflow⟩
        have hJ0 : 0 ≤ J m := hJnonneg m
        have hJD : J m ≤ D := (hJle m hm).trans hsD
        have hJcenter : D ≤ 2 * J m + 2 := hcenterBound m
        have hRprev0 : 0 ≤ R m := hRnonneg m
        have hRprevU : R m ≤ u := hRle m hm
        have ha : 0 ≤ evenQangle M Q (J m) := by
          rw [hangleCoord]
          positivity
        have hRleReal : (R m : ℝ) ≤ (u : ℝ) := by exact_mod_cast hRprevU
        have hadvance : ((R m : ℝ) * theta) / 2 + theta ≤
            ((u : ℝ) + 2) * theta / 2 := by
          have hmul := mul_le_mul_of_nonneg_right hRleReal htheta0.le
          nlinarith [hmul]
        have haθ : evenQangle M Q (J m) + theta < Real.pi / 2 := by
          rw [hangleCoord]
          exact hadvance.trans_lt hangleBound
        have hnext := evenQ_ratio_successor M Q hxpos hJ0 hJD hJcenter
          hp hz ha rfl hza haθ
        have hRnext0 : 0 ≤ R (m + 1) := hRnonneg (m + 1)
        have hRnextU : R (m + 1) ≤ u := hRle (m + 1) (by omega)
        have hflowNext : R (m + 1) ^ 2 < U₀ :=
          hflowOfR (m + 1) hRnext0 hRnextU
        have hJsucc : J (m + 1) = J m + 1 := by
          dsimp [J]
          omega
        simpa [P, hJsucc] using
          (show p M Q (J m + 1) ≠ 0 ∧
            0 ≤ evenQratio M Q (J m + 1) ∧
            evenQratio M Q (J m + 1) ≤
              Real.sqrt (evenQLambda M Q) * Real.tan (evenQangle M Q (J m + 1)) ∧
            R (m + 1) ^ 2 < U₀ from
            ⟨hnext.1, hnext.2.1, hnext.2.2, hflowNext⟩)
  have hPend := hpath n le_rfl
  rcases hPend with ⟨hpS, hzS, hzaS, _⟩
  have hJend : J n = s := by dsimp [J]; exact hcn
  have hpS' : p M Q s ≠ 0 := by simpa [hJend] using hpS
  have hzS' : 0 ≤ evenQratio M Q s := by simpa [hJend] using hzS
  have hzaS' : evenQratio M Q s ≤
      Real.sqrt (evenQLambda M Q) * Real.tan (evenQangle M Q s) := by
    simpa [hJend] using hzaS
  have hangleS : evenQangle M Q s = ((u : ℝ) * theta) / 2 := by
    dsimp [evenQangle, u, D, theta]
  have haS : 0 ≤ evenQangle M Q s := by
    rw [hangleS]
    positivity
  have haSθ : evenQangle M Q s + theta < Real.pi / 2 := by
    rw [hangleS]
    nlinarith [hangleBound]
  have hthetaArg : theta = Real.arctan
      (Real.sqrt (evenQLambda M Q) / (x : ℝ)) := by
    dsimp [theta, evenQtheta]
    rw [← hxRdef]
  have hthetaExpected : 0 < Real.arctan
      (Real.sqrt (evenQLambda M Q) / (x : ℝ)) := by
    rw [← hthetaArg]
    exact htheta0
  have haSθ' : evenQangle M Q s +
      Real.arctan (Real.sqrt (evenQLambda M Q) / (x : ℝ)) < Real.pi / 2 := by
    rw [← hthetaArg]
    exact haSθ
  have htanBound := evenQ_bound_lt_x (x := (x : ℝ)) hxR hLambda haS
    hthetaExpected haSθ'
  have hzltx : evenQratio M Q s < (x : ℝ) := lt_of_le_of_lt hzaS' htanBound
  have hpsR : (p M Q s : ℝ) ≠ 0 := by exact_mod_cast hpS'
  have hdevRatio : (evenQdev M Q s : ℝ) =
      -evenQratio M Q s * (p M Q s : ℝ) := by
    dsimp [evenQratio]
    field_simp [hpsR]
  have hpnrelZ : (D + 2) * p M Q (s + 1) = x * p M Q s + evenQdev M Q s := by
    dsimp [D, x, evenQdev]
    ring
  have hpnrelR : ((D : ℝ) + 2) * (p M Q (s + 1) : ℝ) =
      (x : ℝ) * (p M Q s : ℝ) + (evenQdev M Q s : ℝ) := by
    exact_mod_cast hpnrelZ
  have hpnrelR' : ((D : ℝ) + 2) * (p M Q (s + 1) : ℝ) =
      (p M Q s : ℝ) * ((x : ℝ) - evenQratio M Q s) := by
    rw [hdevRatio] at hpnrelR
    nlinarith [hpnrelR]
  have hpnRatio : (p M Q (s + 1) : ℝ) =
      (p M Q s : ℝ) * ((x : ℝ) - evenQratio M Q s) / ((D : ℝ) + 2) := by
    field_simp [hDplus.ne']
    nlinarith [hpnrelR']
  have hprodPos : 0 < (p M Q (s + 1) : ℝ) * (p M Q s : ℝ) := by
    rw [hpnRatio]
    have hsq : 0 < (p M Q s : ℝ) ^ 2 := sq_pos_of_ne_zero hpsR
    have hid :
        ((p M Q s : ℝ) * ((x : ℝ) - evenQratio M Q s) / ((D : ℝ) + 2)) *
            (p M Q s : ℝ) =
          ((p M Q s : ℝ) ^ 2 * ((x : ℝ) - evenQratio M Q s)) / ((D : ℝ) + 2) := by
      ring
    rw [hid]
    exact div_pos (mul_pos hsq (sub_pos.mpr hzltx)) hDplus
  have hprodDevR : (p M Q (s + 1) : ℝ) * (evenQdev M Q s : ℝ) ≤ 0 := by
    have hid : (p M Q (s + 1) : ℝ) * (evenQdev M Q s : ℝ) =
        -evenQratio M Q s * ((p M Q (s + 1) : ℝ) * (p M Q s : ℝ)) := by
      rw [hdevRatio]
      ring
    rw [hid]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hzS') hprodPos.le
  have hprodDev : p M Q (s + 1) * evenQdev M Q s ≤ 0 := by
    exact_mod_cast hprodDevR
  have hTurPos := evenQ_tur_pos M Q hQM hs hg
  let A : ℤ := D + 1 - s
  have hA : 0 < A := by dsimp [A]; omega
  have hcoeff : 0 < (s + 2) * A := mul_pos (by omega) hA
  have hfirst : 0 < (u + 2) * A * Tur M Q s :=
    mul_pos (mul_pos (by omega) hA) hTurPos
  have hstepRaw : (s + 2) * A * T M Q s =
      (u + 2) * A * Tur M Q s - p M Q (s + 1) * evenQdev M Q s := by
    have h := evenQ_step_identity M Q s
    have hbase : (s + 2) * (D + 1 - s) * T M Q s =
        (2 * (s + 1) - D) * (D + 1 - s) * Tur M Q s -
          p M Q (s + 1) * evenQdev M Q s := by
      simpa [D, evenQdev] using h
    have hcoefEq : 2 * (s + 1) - D = u + 2 := by dsimp [u]; ring
    calc
      (s + 2) * A * T M Q s =
          (s + 2) * (D + 1 - s) * T M Q s := by simp [A]
      _ = (2 * (s + 1) - D) * (D + 1 - s) * Tur M Q s -
            p M Q (s + 1) * evenQdev M Q s := hbase
      _ = (u + 2) * A * Tur M Q s -
            p M Q (s + 1) * evenQdev M Q s := by rw [hcoefEq]
  have hTpos : 0 < T M Q s := by
    have hrhs : 0 < (u + 2) * A * Tur M Q s -
        p M Q (s + 1) * evenQdev M Q s := by linarith
    by_contra hnot
    have hTnonpos : T M Q s ≤ 0 := le_of_not_gt hnot
    have hleft := mul_nonpos_of_nonneg_of_nonpos hcoeff.le hTnonpos
    rw [hstepRaw] at hleft
    linarith
  exact hTpos.le

end Kraw
