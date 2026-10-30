import CatalanCore.Uniform.Content.BankShared.FixedBudget
set_option Elab.async false
namespace CatalanCore.Uniform.Content.BankShared
/-- Any compact prime band bounds the scale of fixed primes and higher levels. -/
theorem compact_bad_scale (K P D r p : ℕ) (hp : 0 < p) (hband : r ≤ K * p)
    (hbad : p ≤ P ∨ p * p ≤ D * r) : r ≤ K * P + D * K * K := by
  rcases hbad with hfix | hsq
  · have h := Nat.mul_le_mul_left K hfix
    omega
  · have hmul : p * p ≤ (D * K) * p := by
      calc p * p ≤ D * r := hsq
           _ ≤ D * (K * p) := Nat.mul_le_mul_left D hband
           _ = _ := by ring
    have hpK : p ≤ D * K := by
      by_contra h
      have hh := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge h) hp
      omega
    have h := Nat.mul_le_mul_left K hpK
    nlinarith
#print axioms compact_bad_scale
end CatalanCore.Uniform.Content.BankShared