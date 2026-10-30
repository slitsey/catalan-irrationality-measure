import CatalanCore.Uniform.Bank.Lambda.M3
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.M3Bounds
/-- Exact rounded M3 gap price for this profile piece. -/
theorem C3P11_bound (r m p k o : ℕ) (ho : o = 1 ∨ o = 3)
    (hk : 4 * k = 3 * p + o)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5)
    (hleft : 11 * r ≤ 90 * p)
    (hright : 65 * p ≤ 8 * r) :
    (5 : ℤ) * (((2 * r + 2 * m : ℕ) : ℤ) -
      ((m3Upper r m p k 8 8 0 - m3Lower r m p k 8 8 0 : ℕ) : ℤ)) ≤
      (17 : ℤ) * r + (-50 : ℤ) * p + 50 := by
  unfold m3Upper m3Lower
  omega
#print axioms C3P11_bound
end CatalanCore.Uniform.Bank.Lambda.M3Bounds
