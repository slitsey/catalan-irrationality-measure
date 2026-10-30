import CatalanCore.Uniform.Content.Layers.SawCount
set_option Elab.async false
namespace CatalanCore.Uniform.Content.Wire
open CatalanCore.Uniform.Content.Layers
/-- Any triangle about a fixed multiple is bounded by the true modular saving. -/
theorem saw_triangle (p m n : ℕ) (hp : 0 < p) :
    min (m - n * p) (n * p + p - m) ≤ sawM p m := by
  by_cases h : n * p ≤ m
  · simpa only [sawM, Nat.add_mul, one_mul] using dist_ge p m n hp h
  · have hz : m - n * p = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz, zero_min]
    exact Nat.zero_le _
#print axioms saw_triangle
end CatalanCore.Uniform.Content.Wire