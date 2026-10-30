import CatalanCore.Uniform.Content.Wire.SawPrice
import CatalanCore.Arith.Hybrid.D1Exact
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Layers
open CatalanCore.Uniform.Content.Wire

/-- Ascending sawtooth branch with the actual one-fifth border rounding. -/
theorem saw_price_up (V r m p n : ℕ) (hp : 0 < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5)
    (hv : V + sawM p m ≤ 2 * (r + m))
    (hlo : 10 * (n * p) ≤ r) (hhi : r ≤ 10 * (n * p) + 5 * p) :
    10 * V ≤ 21 * r + 10 * (n * p) + 40 := by
  have ht := saw_triangle p m n hp
  omega

/-- Descending sawtooth branch, including all integer endpoint cases. -/
theorem saw_price_down (V r m p n : ℕ) (hp : 0 < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5)
    (hv : V + sawM p m ≤ 2 * (r + m))
    (hlo : 10 * (n * p) + 5 * p ≤ r) (hhi : r ≤ 10 * (n * p + p)) :
    10 * V + 10 * (n * p + p) ≤ 23 * r + 40 := by
  have ht := saw_triangle p m n hp
  omega

theorem saw_trop_up (lev : ℕ → ℕ → ℕ) (r m p n : ℕ) (hp : p % 2 = 1)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5)
    (hlo : 10 * (n * p) ≤ r) (hhi : r ≤ 10 * (n * p) + 5 * p) :
    10 * tropVal (HW lev p r m) ≤ 21 * r + 10 * (n * p) + 40 :=
  saw_price_up _ r m p n (by omega) hm1 hm2 (trop_saw_closed lev hp) hlo hhi

theorem saw_trop_down (lev : ℕ → ℕ → ℕ) (r m p n : ℕ) (hp : p % 2 = 1)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5)
    (hlo : 10 * (n * p) + 5 * p ≤ r) (hhi : r ≤ 10 * (n * p + p)) :
    10 * tropVal (HW lev p r m) + 10 * (n * p + p) ≤ 23 * r + 40 :=
  saw_price_down _ r m p n (by omega) hm1 hm2 (trop_saw_closed lev hp) hlo hhi

#print axioms saw_price_up
#print axioms saw_price_down
end CatalanCore.Uniform.Bank.Lambda