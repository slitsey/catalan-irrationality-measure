import CatalanCore.Uniform.Bank.Lambda.Rounding
import CatalanCore.Uniform.Bank.Lambda.TwoTerm
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda

/-- Exact rounding at the first strict-LP cut, including parity. -/
theorem lp1_size_of_cut (r m p : ℕ) (hr : r % 2 = 0)
    (hm : 10 * m ≤ r + 5) (hcut : 3 * r ≤ 5 * p) :
    r + 2 * m ≤ 2 * p := by
  omega

/-- The second leading cut already implies the exact one-based LP window. -/
theorem lp2_size_of_cut (a j r m p k : ℕ) (ha : a = 1 ∨ a = 3)
    (hj : j = 1 ∨ j = 3) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hm : 10 * m ≤ r + 5) (hk : 4 * k = j * p + (4 - a))
    (hcut : 24 * r ≤ 5 * (4 + j) * p) : r + 2 * m ≤ p + k := by
  rcases ha with rfl | rfl <;> rcases hj with rfl | rfl <;> omega

/-- The pole remains within the common block on the second strict-LP window. -/
theorem lp2_pole_le_scale (a j r m p k : ℕ) (ha : a = 1 ∨ a = 3)
    (hj : j = 1 ∨ j = 3) (hp : 29 ≤ p) (hm : 10 * m ≤ r + 5)
    (hk : 4 * k = j * p + (4 - a)) (hupper : p < r + m) : k ≤ r := by
  rcases ha with rfl | rfl <;> rcases hj with rfl | rfl <;> omega

#print axioms lp1_size_of_cut
#print axioms lp2_size_of_cut
#print axioms lp2_pole_le_scale
end CatalanCore.Uniform.Bank.Lambda
