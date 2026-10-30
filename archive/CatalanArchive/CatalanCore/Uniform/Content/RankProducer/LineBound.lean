import Mathlib.Tactic
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer

/-- Turn the actual balanced line counts into their affine upper price.
The two upper and lower kill-count errors account for every discarded kill. -/
theorem price_le_line_of_counts (P K R C S T W H : ℕ) (L E U B F : ℚ)
    (hK : K = min R C) (hcost : P + max K (S + T) ≤ 2 * H)
    (htrim : W ≤ S + T + (R - K) + (C - K))
    (hR : L - E ≤ (R : ℚ) ∧ (R : ℚ) ≤ L + U)
    (hC : L - E ≤ (C : ℚ) ∧ (C : ℚ) ≤ L + U)
    (hW : B - F ≤ (W : ℚ)) :
    (P : ℚ) ≤ 2 * (H : ℚ) - B + F + 2 * (E + U) := by
  have hKR : K ≤ R := by rw [hK]; exact min_le_left R C
  have hKC : K ≤ C := by rw [hK]; exact min_le_right R C
  have hKL : L - E ≤ (K : ℚ) := by
    rw [hK]
    rcases le_total R C with h | h
    · rw [min_eq_left h]; exact hR.1
    · rw [min_eq_right h]; exact hC.1
  have hP : P + (S + T) ≤ 2 * H := by omega
  have hPQ : (P : ℚ) + ((S : ℚ) + T) ≤ 2 * (H : ℚ) := by exact_mod_cast hP
  have hTQ : (W : ℚ) ≤ (S : ℚ) + T + ((R - K : ℕ) : ℚ) + ((C - K : ℕ) : ℚ) := by exact_mod_cast htrim
  rw [Nat.cast_sub hKR, Nat.cast_sub hKC] at hTQ
  linarith [hR.2, hC.2]

#print axioms price_le_line_of_counts
end CatalanCore.Uniform.Content.RankProducer
