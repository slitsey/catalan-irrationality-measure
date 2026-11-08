module

public import CatalanMeasure.GenD.Signed.RouteI.ShiftGLeaf

@[expose] public section

/-!
# G5 shiftG, leaf instances: column sups hY, second population

For each knot `γ`: `2 T(dv, s) + γ log (1 + 3 s/4) ≤ Y_γ` on `[0,1]` (`dv = dv40`, scale `2^-24`), `Y_γ` = the true sup rounded up by at least 2e-8 on the 1e-8 grid. The log is replaced by `logW` (degree 65, Mathlib `abs_log_sub_add_sum_range_le`, `log_le_logW`). Each knot is one kernel decision `checkZ` on an integer polynomial built in the kernel.
-/

open Set

namespace CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY2a
open CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance CatalanMeasure.GenD.Signed.RouteI.T4Instance
  CatalanMeasure.GenD.Signed.RouteI.ShiftGLeaf OAI.InternalCatalan

noncomputable section

theorem div : divOK 5342931457063200 40 = true := by decide +kernel

theorem dv_div (k : ℕ) (hk : k < dv40.length) : ((k : ℤ) + 1) ∣ 5342931457063200 := by
  rw [len_dv40] at hk; exact divOK_spec div hk

theorem Y2_51_500_check : checkZ (addL (combZ (13909310 * 2 ^ 24 * 5342931457063200 * 4 ^ 65 * L64 * 500)
    (wts (-2 * 4 ^ 65 * L64 * 500 * 10 ^ 8) 5342931457063200 dv40) [])
    (smulL (-(51 * 2 ^ 24 * 5342931457063200 * 10 ^ 8)) (0 :: logW))) 11 0 0 = true := by
  decide +kernel -- kcost: 96.80 s measured (standalone, profiler type checking); 129 cellOK calls (mirror) of a degree-66 polynomial

/-- `γ = 51/500`, true sup 0.1390930786 (at s = 0.997430). -/
theorem Y2_51_500_leaf : ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv40 (2 ^ 24)) s +
    (51 / 500 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ (13909310 : ℝ) / 10 ^ 8 := by
  have h := leafY (Λ := 5342931457063200) (by norm_num) dv40 dv_div 51 500 13909310 (10 ^ 8) (by norm_num)
    (by norm_num) (by norm_num) Y2_51_500_check
  simpa only [Int.cast_ofNat, Int.cast_pow, Int.cast_one] using h


end

end CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY2a
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY2a.Y2_51_500_leaf
