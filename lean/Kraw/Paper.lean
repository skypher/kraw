import Kraw.Main
import Kraw.GLChar
import Kraw.Krawtchouk
import Kraw.Examples
import Kraw.Normalization
import Kraw.Remarks
import Kraw.OddPublic
import Kraw.CertTable

/-!
# Index: every numbered statement and displayed claim of the paper

Paper: *Monotonicity of Turán determinants for binary Krawtchouk polynomials*, Version 2.0.3.
Each alias below carries the exact statement proved in the file named in its docstring.
-/

open MvPolynomial

namespace Kraw.Paper

open Kraw

/-! ## §1.1 -/
/-- §1.1: `p_s = K_s(Q;D)` (`Krawtchouk.lean`). -/
alias p_eq_K := p_eq_krawtchouk
/-- §1.1: the generating function of `K_k(x;N)` (`Krawtchouk.lean`). -/
alias K_genfun := krawtchouk_genfun
/-- §1.1: `K_s(·;D)` has degree `s` (`Krawtchouk.lean`). -/
alias K_degree := krawtchouk_natDegree
/-- Theorem 1.1 (`Main.lean`). -/
alias theorem_1_1 := main_theorem
/-- Theorem 1.1, equivalent form (`Main.lean`). -/
alias theorem_1_1_nonincreasing := Tur_antitone_top
/-- Theorem 1.1: symmetry `Tur(D-s) = Tur(s)` (`Basic.lean`). -/
alias theorem_1_1_symmetric := Tur_refl
/-- Theorem 1.1: weak unimodality, bottom half (`Remarks.lean`). -/
alias theorem_1_1_unimodal_left := Tur_monotone_left
/-- Theorem 1.1: weak unimodality, top half (`Remarks.lean`). -/
alias theorem_1_1_unimodal_right := Tur_antitone_right
/-- Corollary 1.2(1) (`Main.lean`). -/
alias corollary_1_2_i := Tur_ge_one
/-- Corollary 1.2(1), sharpness: `Tur(D) = 1` (`Basic.lean`). -/
alias corollary_1_2_i_sharp := Tur_top
/-- Corollary 1.2(2) (`Main.lean`). -/
alias corollary_1_2_ii := Tur_le_center
/-- §1.1 example `(M,Q) = (5,2)` (`Examples.lean`). -/
alias example_coefficients := example_p
alias example_turan := example_Tur
/-- §1.1: the real relaxation fails (`Examples.lean`). -/
alias real_relaxation := real_relaxation_counterexample
alias real_relaxation_consistent := pReal_natCast

/-! ## §1.2 -/
/-- Proposition 1.3: `Tur(s) = s_{(2^s)}(z)` (`SchurProp.lean`). -/
alias proposition_1_3 := tur_eq_schur
/-- Proposition 1.3: irreducible polynomial character of `GL_D(ℂ)` (`GLChar.lean`). -/
alias proposition_1_3_character := tur_irreducible_character
/-- Proposition 1.3: `s_{(2^s)}(z) = s_{(2^{D-s})}(z)` (`SchurProp.lean`). -/
alias proposition_1_3_symmetry := schur_rect_symm
/-- Proof of Proposition 1.3: the rectangle-complement identity (`SchurProp.lean`). -/
alias proposition_1_3_complement := schur_complement
/-- Proof of Proposition 1.3: dual Jacobi–Trudi for two columns (`SchurJT.lean`). -/
alias dual_jacobi_trudi := schur_twoCol
alias dual_jacobi_trudi_one_column := schur_twoCol_zero
/-- Proof of Proposition 1.3: `p_r = e_r(z)` (`SchurProp.lean`). -/
alias p_eq_esymm := p_eq_esymm_zSign

/-- §1.2: the rectangular character values are positive integers ... -/
theorem character_values_pos (M Q : ℕ) {s : ℕ} (hs : s ≤ M + Q) :
    1 ≤ eval (zSign M Q) (schur (rect s) (M + Q)) := by
  rw [← tur_eq_schur M Q hs]
  exact Tur_ge_one M Q (by positivity) (by exact_mod_cast hs)

/-- §1.2: ... forming a symmetric sequence ... -/
theorem character_values_symm (M Q : ℕ) {s : ℕ} (hs : s ≤ M + Q) :
    eval (zSign M Q) (schur (rect s) (M + Q)) =
      eval (zSign M Q) (schur (rect (M + Q - s)) (M + Q)) :=
  schur_rect_symm M Q hs

/-- §1.2: ... that is weakly unimodal in the rectangle height (top half). -/
theorem character_values_unimodal_right (M Q : ℕ) {s t : ℕ} (hs : M + Q ≤ 2 * s) (hst : s ≤ t)
    (ht : t ≤ M + Q) :
    eval (zSign M Q) (schur (rect t) (M + Q)) ≤ eval (zSign M Q) (schur (rect s) (M + Q)) := by
  rw [← tur_eq_schur M Q ht, ← tur_eq_schur M Q (le_trans hst ht)]
  exact_mod_cast Tur_antitone_right M Q (s := s) (t := t) (by exact_mod_cast hs) (by exact_mod_cast hst)

/-- §1.2: ... and in the bottom half. -/
theorem character_values_unimodal_left (M Q : ℕ) {s t : ℕ} (hst : s ≤ t) (ht : 2 * t ≤ M + Q + 1)
    (htD : t ≤ M + Q) :
    eval (zSign M Q) (schur (rect s) (M + Q)) ≤ eval (zSign M Q) (schur (rect t) (M + Q)) := by
  rw [← tur_eq_schur M Q htD, ← tur_eq_schur M Q (le_trans hst htD)]
  exact Tur_monotone_left M Q (by positivity) (by exact_mod_cast hst) (by exact_mod_cast ht)

/-- §1.2: Schur polynomials can take negative values at `±1` specializations
(`s_{(1)}(-1) = -1`), so Schur positivity alone does not fix the sign of `Tur(s)`. -/
theorem schur_value_can_be_negative :
    eval (fun _ : Fin 1 => (-1 : ℤ)) (schur (twoCol 1 0 (Nat.zero_le 1)) 1) = -1 := by
  rw [schur_twoCol_zero, MvPolynomial.esymm]
  simp [Finset.powersetCard_one]

/-! ## §1.3 -/
alias normalization_rescale := turan_rescale_iff
alias normalization_geometric := log_flat_iff_geometric
alias orthonormal_fails := orthonormal_not_monotone
alias endpoint_fails := endpoint_not_monotone
/-- Supporting result, not itself a claim of the paper: orthogonality of the Krawtchouk
polynomials, which gives the norms used in §1.3. -/
alias K_orthogonality := krawtchouk_orthogonal

/-! ## §1.4 and §2 -/
/-- §2: cells satisfy `u ≡ x ≡ D (mod 2)`. -/
theorem cell_parity (M Q : ℕ) (s : ℤ) :
    (2 * s - ((M : ℤ) + Q)) % 2 = ((M : ℤ) + Q) % 2 ∧ ((M : ℤ) - Q) % 2 = ((M : ℤ) + Q) % 2 := by
  omega

alias swap_invariance := T_swap
alias swap_coefficients := p_swap
alias recurrence_2_1 := p_rec
alias reflection := p_refl
alias top_value := p_top
alias top_value_sub_one := p_top_sub_one
alias lemma_2_1 := no_consec_zero

/-! ## §3 -/
alias theorem_3_1_identity := qform
alias theorem_3_1_rational := quadForm_rational
alias theorem_3_1_discriminant := disc_rational
alias theorem_3_1_bulk := T_nonneg_bulk
alias remark_3_1_shift := shift_two_basis
alias remark_3_1_step := stepMat_spec
alias remark_3_1_step_det := stepMat_det
alias remark_3_1_psd := psd_congr
alias theorem_3_2 := T_center
alias theorem_3_2_odd := center_odd
alias theorem_3_2_even := center_even
alias theorem_3_2_equality := T_center_eq_zero_iff
alias theorem_3_3 := T_nonneg_flow
alias theorem_3_3_condition := flow_condition_iff
alias corollary_3_4 := coverage
alias corollary_3_4_D0 := T_zero_zero
alias corollary_3_4_q := q_identity
alias corollary_3_4_boundary := q_flow_boundary_nonpos
alias corollary_3_4_x_pos := gap_x_pos
alias lemma_3_5 := gap_hered
alias lemma_3_6 := gap_strip
alias lemma_3_6_Q_pos := gap_strip_Q_pos
alias first_odd_gap := first_odd_gap_cell

/-! ## §4 and §5 -/
alias theorem_4_1 := T_nonneg_gap_even
alias proposition_5_1 := prop_5_1
alias proposition_5_1_sign := T_odd_u1
alias window_5_1 := window_identity
alias window_discriminant := window_disc
alias lemma_5_2_transition := lemma_5_2
alias lemma_5_2_odd_base := lemma_5_2_base
alias theorem_5_3 := T_nonneg_gap_odd

/-! ## Lemma 5.2: coefficient table of `O₁`–`O₄` -/
alias table_O1 := cO1_table
alias table_O2 := cO2_table
alias table_O3 := cO3_table
alias table_O4 := cO4_table
alias table_P1_R1 := cP1_cR1_spec
alias table_O4_form := cO4X_spec

end Kraw.Paper
