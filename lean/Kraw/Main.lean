import Kraw.Flow
import Kraw.EvenQ
import Kraw.OddQ

/-!
# Assembly: the Main Theorem and its corollaries

Paper §6 (assembly), Theorem 1.1 and Corollary 1.2.
-/

namespace Kraw

/-- Main Theorem under the normalization `Q ≤ M` (paper §6, cases (1)–(5)). -/
theorem main_of_le (M Q : ℕ) (hQM : Q ≤ M) {s : ℤ} (h1 : (M : ℤ) + Q ≤ 2 * s)
    (h2 : s ≤ (M : ℤ) + Q) : 0 ≤ T M Q s := by
  rcases eq_or_lt_of_le h2 with hsD | hsD
  · rw [hsD, T_top]; norm_num
  rcases eq_or_lt_of_le h1 with hc | hc
  · exact T_center M Q hc.symm
  have hu1 : 1 ≤ 2 * s - ((M : ℤ) + Q) := by omega
  by_cases hb : ((M : ℤ) - Q) ^ 2 * (2 * s - ((M : ℤ) + Q) + 1) ^ 2 ≤
      ((2 * s - ((M : ℤ) + Q) + 1) ^ 2 - 1) *
        (((M : ℤ) + Q + 3) ^ 2 - (2 * s - ((M : ℤ) + Q) + 1) ^ 2)
  · exact T_nonneg_bulk M Q hu1 h2 hb
  by_cases hf : ((M : ℤ) + Q + 1) ^ 2 - ((M : ℤ) - Q) ^ 2 ≤ (2 * s - ((M : ℤ) + Q) + 1) ^ 2
  · exact T_nonneg_flow M Q hQM h1 hsD hf
  have hg : Gap ((M : ℤ) + Q) ((M : ℤ) - Q) (2 * s - ((M : ℤ) + Q)) :=
    ⟨hu1, lt_of_not_ge hb, lt_of_not_ge hf⟩
  rcases Nat.even_or_odd Q with hQ | hQ
  · exact T_nonneg_gap_even M Q hQM hQ h2 hg
  · rcases eq_or_lt_of_le hu1 with hu | hu
    · exact T_odd_u1 M Q hQ (by omega)
    · exact T_nonneg_gap_odd M Q hQM hQ h2 (by omega) hg

/-- **Main Theorem 1.1.** For all `M Q ≥ 0` and `⌈D/2⌉ ≤ s ≤ D`, `T_s ≥ 0`. -/
theorem main_theorem (M Q : ℕ) {s : ℤ} (h1 : (M : ℤ) + Q ≤ 2 * s) (h2 : s ≤ (M : ℤ) + Q) :
    0 ≤ T M Q s := by
  rcases le_total Q M with hQM | hMQ
  · exact main_of_le M Q hQM h1 h2
  · rw [← T_swap M Q s]
    exact main_of_le Q M hMQ (by omega) (by omega)

/-- Equivalent form: `Tur` is non-increasing on the top half. -/
theorem Tur_antitone_top (M Q : ℕ) {s : ℤ} (h1 : (M : ℤ) + Q ≤ 2 * s)
    (h2 : s ≤ (M : ℤ) + Q) : Tur M Q (s + 1) ≤ Tur M Q s := by
  have h := main_theorem M Q h1 h2
  unfold T at h
  linarith

theorem Tur_ge_one_top (M Q : ℕ) (n : ℕ) :
    ∀ s : ℤ, s = (M : ℤ) + Q - n → (M : ℤ) + Q ≤ 2 * s → 1 ≤ Tur M Q s := by
  induction n with
  | zero =>
    intro s hs _
    rw [hs, Nat.cast_zero, sub_zero, Tur_top]
  | succ n ih =>
    intro s hs h1
    have h2 : s ≤ (M : ℤ) + Q := by omega
    have hstep := Tur_antitone_top M Q h1 h2
    have hnext := ih (s + 1) (by push_cast at hs; omega) (by omega)
    linarith

/-- **Corollary 1.2(1).** `Tur(s) ≥ 1` for every `0 ≤ s ≤ D`. -/
theorem Tur_ge_one (M Q : ℕ) {s : ℤ} (h0 : 0 ≤ s) (h2 : s ≤ (M : ℤ) + Q) :
    1 ≤ Tur M Q s := by
  rcases le_total ((M : ℤ) + Q) (2 * s) with h1 | h1
  · exact Tur_ge_one_top M Q ((M : ℤ) + Q - s).toNat s (by omega) h1
  · rw [← Tur_refl M Q s]
    exact Tur_ge_one_top M Q s.toNat _ (by omega) (by omega)

/-- **Corollary 1.2(2).** `Tur(s) ≤ Tur(⌈D/2⌉)` for every `0 ≤ s ≤ D`. -/
theorem Tur_le_center (M Q : ℕ) {s : ℤ} (h0 : 0 ≤ s) (h2 : s ≤ (M : ℤ) + Q) :
    Tur M Q s ≤ Tur M Q (((M : ℤ) + Q + 1) / 2) := by
  have key : ∀ n : ℕ, ∀ t : ℤ, t = ((M : ℤ) + Q + 1) / 2 + n → t ≤ (M : ℤ) + Q →
      Tur M Q t ≤ Tur M Q (((M : ℤ) + Q + 1) / 2) := by
    intro n
    induction n with
    | zero => intro t ht _; rw [ht, Nat.cast_zero, add_zero]
    | succ n ih =>
      intro t ht htD
      have hprev := ih (t - 1) (by push_cast at ht; omega) (by omega)
      have hstep := Tur_antitone_top M Q (s := t - 1) (by omega) (by omega)
      rw [sub_add_cancel] at hstep
      linarith
  rcases le_or_gt (((M : ℤ) + Q + 1) / 2) s with h1 | h1
  · exact key (s - ((M : ℤ) + Q + 1) / 2).toNat s (by omega) h2
  · rw [← Tur_refl M Q s]
    exact key ((M : ℤ) + Q - s - ((M : ℤ) + Q + 1) / 2).toNat _ (by omega) (by omega)

end Kraw
