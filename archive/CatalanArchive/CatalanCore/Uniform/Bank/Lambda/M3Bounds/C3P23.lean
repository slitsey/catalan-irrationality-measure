import CatalanCore.Uniform.Bank.Lambda.M3
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.M3Bounds
/-- Exact rounded M3 gap price for this profile piece. -/
theorem C3P23_bound (r m p k o : ℕ) (ho : o = 1 ∨ o = 3)
    (hk : 4 * k = 3 * p + o)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5)
    (hleft : 6 * r ≤ 35 * p)
    (hright : 23 * p ≤ 4 * r) :
    (20 : ℤ) * (((2 * r + 2 * m : ℕ) : ℤ) -
      ((m3Upper r m p k 6 5 0 - m3Lower r m p k 6 5 0 : ℕ) : ℤ)) ≤
      (44 : ℤ) * r + (-15 : ℤ) * p + 200 := by
  unfold m3Upper m3Lower
  omega
#print axioms C3P23_bound
end CatalanCore.Uniform.Bank.Lambda.M3Bounds
