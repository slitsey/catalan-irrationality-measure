import Mathlib.Tactic
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer

/-- Affine count errors and arbitrary balanced trimming cost only six fixed errors. -/
theorem affine_line_price_bound (H K R C MC MR price matches : ℕ) (L G U E : ℚ)
    (hKR : K ≤ R) (hKC : K ≤ C)
    (hK : L - E ≤ (K : ℚ)) (hR : (R : ℚ) ≤ L + E) (hC : (C : ℚ) ≤ L + E)
    (hM : G - 2 * E ≤ (matches : ℚ))
    (hS : matches ≤ MC + MR + (R - K) + (C - K))
    (hP : price + max K (MC + MR) ≤ 2 * H) (hH : ((2 * H : ℕ) : ℚ) ≤ U) :
    (price : ℚ) ≤ U - G + 6 * E := by
  have hPN : price + (MC + MR) ≤ 2 * H :=
    (Nat.add_le_add_left (le_max_right K (MC + MR)) price).trans hP
  have hPQ : (price : ℚ) + (MC : ℚ) + (MR : ℚ) ≤ ((2 * H : ℕ) : ℚ) := by
    exact_mod_cast (show price + MC + MR ≤ 2 * H by omega)
  have hSQ : (matches : ℚ) ≤ (MC : ℚ) + (MR : ℚ) +
      ((R - K : ℕ) : ℚ) + ((C - K : ℕ) : ℚ) := by exact_mod_cast hS
  rw [Nat.cast_sub hKR, Nat.cast_sub hKC] at hSQ
  linarith

#print axioms affine_line_price_bound
end CatalanCore.Uniform.Content.RankProducer
