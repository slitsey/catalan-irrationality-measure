import CatalanCore.Uniform.Content.Layers.SawCount
import CatalanCore.Arith.Hybrid.D1Exact
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Layers

/-- A triangular branch about any fixed multiple is below the nearest-multiple saving. -/
theorem saw_triangle (p m n : ℕ) (hp : 0 < p) :
    min (m - n * p) (n * p + p - m) ≤ sawM p m := by
  by_cases h : n * p ≤ m
  · simpa only [sawM, Nat.add_mul, one_mul] using dist_ge p m n hp h
  · have hz : m - n * p = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hz, zero_min]
    exact Nat.zero_le _

/-- Ascending sawtooth branch, with a uniform additive error for rounding m. -/
theorem saw_price_up (V r m p n : ℕ) (hp : 0 < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6)
    (hv : V + sawM p m ≤ 2 * (r + m))
    (hlo : 12 * (n * p) ≤ r) (hhi : r ≤ 12 * (n * p) + 6 * p) :
    12 * V ≤ 25 * r + 12 * (n * p) + 48 := by
  have ht := saw_triangle p m n hp
  omega

/-- Descending sawtooth branch, with the same rounding error. -/
theorem saw_price_down (V r m p n : ℕ) (hp : 0 < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6)
    (hv : V + sawM p m ≤ 2 * (r + m))
    (hlo : 12 * (n * p) + 6 * p ≤ r) (hhi : r ≤ 12 * (n * p + p)) :
    12 * V + 12 * (n * p + p) ≤ 27 * r + 48 := by
  have ht := saw_triangle p m n hp
  omega

/-- The leading tropical table supplies the preceding branch-price hypothesis. -/
theorem saw_trop_up (lev : ℕ → ℕ → ℕ) (r m p n : ℕ) (hp : p % 2 = 1)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6)
    (hlo : 12 * (n * p) ≤ r) (hhi : r ≤ 12 * (n * p) + 6 * p) :
    12 * tropVal (HW lev p r m) ≤ 25 * r + 12 * (n * p) + 48 :=
  saw_price_up _ r m p n (by omega) hm1 hm2 (trop_saw_closed lev hp) hlo hhi

theorem saw_trop_down (lev : ℕ → ℕ → ℕ) (r m p n : ℕ) (hp : p % 2 = 1)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6)
    (hlo : 12 * (n * p) + 6 * p ≤ r) (hhi : r ≤ 12 * (n * p + p)) :
    12 * tropVal (HW lev p r m) + 12 * (n * p + p) ≤ 27 * r + 48 :=
  saw_price_down _ r m p n (by omega) hm1 hm2 (trop_saw_closed lev hp) hlo hhi

#print axioms saw_price_up
#print axioms saw_price_down
end CatalanCore.Uniform.Bank.Sevenths
