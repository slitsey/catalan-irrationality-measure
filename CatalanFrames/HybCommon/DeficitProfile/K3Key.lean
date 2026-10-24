module
public import CatalanFrames.HybCommon.DeficitProfile.K3Pure
@[expose] public section
namespace CatalanFrames.HybCommon

lemma k3_min_lin (Z c : ℤ) (hc : 0 ≤ c) (m R L sz T : ℕ)
    (h1 : Z ≤ c * m)
    (h2 : Z ≤ 0 ∨ (L + m ≤ R ∧ (Z ≤ c * (((R:ℤ) - L) - m) ∨
      (sz ≤ T ∧ Z ≤ c * (2 * (((R:ℤ) - L) - m))) ∨
      (T ≤ sz ∧ Z ≤ c * (2 * (((R:ℤ) - L) - m) - ((sz:ℤ) - T)))))) :
    Z ≤ c * ((min m (((R - L) - m) + (((R - L) - m) - (sz - T))) : ℕ) : ℤ) := by
  have h3 : Z ≤ c * ((((R - L) - m) + (((R - L) - m) - (sz - T)) : ℕ) : ℤ) := by
    rcases h2 with h | ⟨hle, h | ⟨hT, h⟩ | ⟨hT, h⟩⟩
    · exact h.trans (mul_nonneg hc (by positivity))
    · refine h.trans (mul_le_mul_of_nonneg_left ?_ hc)
      omega
    · refine h.trans (mul_le_mul_of_nonneg_left ?_ hc)
      omega
    · refine h.trans (mul_le_mul_of_nonneg_left ?_ hc)
      omega
  rcases le_total m (((R - L) - m) + (((R - L) - m) - (sz - T))) with h | h
  · rw [min_eq_left h]; exact h1
  · rw [min_eq_right h]; exact h3

end CatalanFrames.HybCommon
