import CatalanCore.Uniform.Content.BankShared.ExceptionSmall
set_option Elab.async false
namespace CatalanCore.Uniform.Content.BankShared
theorem Ecrude_log_bound (cE : ℕ) (r p : ℕ) (hp : 2 ≤ p) :
    Ecrude cE r p ≤ (2 * (cE + 12)) * r * (Nat.log 2 r + 1) := by
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · subst h0; simp [Ecrude]
  unfold Ecrude
  have h1 : Nat.log p (14 * r) ≤ Nat.log 2 r + 4 := by
    refine (Nat.log_anti_left (by omega) hp).trans ?_
    have hL : r < 2 ^ (Nat.log 2 r + 1) := Nat.lt_pow_succ_log_self (by omega) r
    have : Nat.log 2 (14 * r) < Nat.log 2 r + 5 := by
      refine Nat.log_lt_of_lt_pow (by omega) ?_
      have h16 : 14 * r < 2 ^ (Nat.log 2 r + 5) := by
        have : 2 ^ (Nat.log 2 r + 5) = 16 * 2 ^ (Nat.log 2 r + 1) := by ring
        rw [this]; omega
      exact h16
    omega
  have h2 : 3 * Nat.log p (14 * r) + cE ≤ (cE + 12) * (Nat.log 2 r + 1) := by nlinarith [Nat.zero_le (cE * Nat.log 2 r)]
  calc 2 * r * (3 * Nat.log p (14 * r) + cE) ≤ 2 * r * ((cE + 12) * (Nat.log 2 r + 1)) :=
        Nat.mul_le_mul_left _ h2
    _ = (2 * (cE + 12)) * r * (Nat.log 2 r + 1) := by ring

#print axioms Ecrude_log_bound
end CatalanCore.Uniform.Content.BankShared
