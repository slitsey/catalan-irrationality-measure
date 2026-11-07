module

public import CatalanCore.Uniform.Bank.Chi3Content.Log

@[expose] public section

/-!
# The refined per-prime weight and the old first piece (lane B, B3c)
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.P6 CatalanFrames.P6Hybrid

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

namespace CatalanCore.Uniform.Bank.Chi3Content

/-- The weight whose class sums are bounded: `min` of the old periodic weight and the refined exponent. -/
noncomputable def Wn (r m p : ℕ) : ℕ := min (Quarter.Periodic.Wsharp r m p) (eExp r m p)

theorem Wn_le_e (r m p : ℕ) : Wn r m p ≤ eExp r m p := min_le_right _ _

theorem Wn_le_W (r m p : ℕ) : Wn r m p ≤ Quarter.W r m p :=
  (min_le_left _ _).trans (Quarter.Periodic.sharp_le r m p)

theorem Wn_le_sharp (r m p : ℕ) : Wn r m p ≤ Quarter.Periodic.Wsharp r m p := min_le_left _ _

/-- The old tropical first piece `11/4 - theta` on `(1/4, 1/2]` (both classes). -/
theorem W_old_first {r m p : ℕ} (hm1 : r ≤ 4 * m) (hm2 : 4 * m ≤ r + 3) (hr : 100 ≤ r)
    (hc : p % 6 = 1 ∨ p % 6 = 5) (hlo : r / 4 < p) (hhi : p ≤ r / 2) :
    4 * (Quarter.W r m p : ℤ) ≤ 11 * r - 4 * p + 100 := by
  have hk := kq6_cases p
  unfold Quarter.W Sv Hb
  split_ifs <;> omega

end CatalanCore.Uniform.Bank.Chi3Content
