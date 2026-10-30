import CatalanCore.Uniform.Bank.Lambda.M3
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.M3Bounds
/-- Exact rounded M3 gap price for this profile piece. -/
theorem C1P08_bound (r m p k o : ℕ) (ho : o = 1 ∨ o = 3)
    (hk : 4 * k = 1 * p + o)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5)
    (hleft : 22 * r ≤ 185 * p)
    (hright : 25 * p ≤ 3 * r) :
    (20 : ℤ) * (((2 * r + 2 * m : ℕ) : ℤ) -
      ((m3Upper r m p k 9 8 0 - m3Lower r m p k 9 8 0 : ℕ) : ℤ)) ≤
      (68 : ℤ) * r + (-205 : ℤ) * p + 200 := by
  unfold m3Upper m3Lower
  omega
#print axioms C1P08_bound
end CatalanCore.Uniform.Bank.Lambda.M3Bounds
