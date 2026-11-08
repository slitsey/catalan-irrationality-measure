module

public import CatalanMeasure.GenD.Signed.RouteI.ShiftGLeaf

@[expose] public section

/-!
# G5 shiftG, leaf instances: column sups hY, second population

For each knot `γ`: `2 T(dv, s) + γ log (1 + 3 s/4) ≤ Y_γ` on `[0,1]` (`dv = dv40`, scale `2^-24`), `Y_γ` = the true sup rounded up by at least 2e-8 on the 1e-8 grid. The log is replaced by `logW` (degree 65, Mathlib `abs_log_sub_add_sum_range_le`, `log_le_logW`). Each knot is one kernel decision `checkZ` on an integer polynomial built in the kernel.
-/

open Set

namespace CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY2b
open CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance CatalanMeasure.GenD.Signed.RouteI.T4Instance
  CatalanMeasure.GenD.Signed.RouteI.ShiftGLeaf OAI.InternalCatalan

noncomputable section

theorem div : divOK 5342931457063200 40 = true := by decide +kernel

theorem dv_div (k : ℕ) (hk : k < dv40.length) : ((k : ℤ) + 1) ∣ 5342931457063200 := by
  rw [len_dv40] at hk; exact divOK_spec div hk

theorem Y2_1_5_check : checkZ (addL (combZ (19392203 * 2 ^ 24 * 5342931457063200 * 4 ^ 65 * L64 * 5)
    (wts (-2 * 4 ^ 65 * L64 * 5 * 10 ^ 8) 5342931457063200 dv40) [])
    (smulL (-(1 * 2 ^ 24 * 5342931457063200 * 10 ^ 8)) (0 :: logW))) 11 0 0 = true := by
  decide +kernel -- kcost: 13.10 s measured (standalone, profiler type checking); 25 cellOK calls (mirror) of a degree-66 polynomial

/-- `γ = 1/5`, true sup 0.1939220074 (at s = 0.999999). -/
theorem Y2_1_5_leaf : ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv40 (2 ^ 24)) s +
    (1 / 5 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ (19392203 : ℝ) / 10 ^ 8 := by
  have h := leafY (Λ := 5342931457063200) (by norm_num) dv40 dv_div 1 5 19392203 (10 ^ 8) (by norm_num)
    (by norm_num) (by norm_num) Y2_1_5_check
  simpa only [Int.cast_ofNat, Int.cast_pow, Int.cast_one] using h

theorem Y2_3_10_check : checkZ (addL (combZ (24989188 * 2 ^ 24 * 5342931457063200 * 4 ^ 65 * L64 * 10)
    (wts (-2 * 4 ^ 65 * L64 * 10 * 10 ^ 8) 5342931457063200 dv40) [])
    (smulL (-(3 * 2 ^ 24 * 5342931457063200 * 10 ^ 8)) (0 :: logW))) 11 0 0 = true := by
  decide +kernel -- kcost: 12.50 s measured (standalone, profiler type checking); 21 cellOK calls (mirror) of a degree-66 polynomial

/-- `γ = 3/10`, true sup 0.2498918557 (at s = 0.999999). -/
theorem Y2_3_10_leaf : ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv40 (2 ^ 24)) s +
    (3 / 10 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ (24989188 : ℝ) / 10 ^ 8 := by
  have h := leafY (Λ := 5342931457063200) (by norm_num) dv40 dv_div 3 10 24989188 (10 ^ 8) (by norm_num)
    (by norm_num) (by norm_num) Y2_3_10_check
  simpa only [Int.cast_ofNat, Int.cast_pow, Int.cast_one] using h

theorem Y2_2_5_check : checkZ (addL (combZ (30584470 * 2 ^ 24 * 5342931457063200 * 4 ^ 65 * L64 * 5)
    (wts (-2 * 4 ^ 65 * L64 * 5 * 10 ^ 8) 5342931457063200 dv40) [])
    (smulL (-(2 * 2 ^ 24 * 5342931457063200 * 10 ^ 8)) (0 :: logW))) 11 0 0 = true := by
  decide +kernel -- kcost: 11.60 s measured (standalone, profiler type checking); 21 cellOK calls (mirror) of a degree-66 polynomial

/-- `γ = 2/5`, true sup 0.3058446764 (at s = 1.000000). -/
theorem Y2_2_5_leaf : ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv40 (2 ^ 24)) s +
    (2 / 5 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ (30584470 : ℝ) / 10 ^ 8 := by
  have h := leafY (Λ := 5342931457063200) (by norm_num) dv40 dv_div 2 5 30584470 (10 ^ 8) (by norm_num)
    (by norm_num) (by norm_num) Y2_2_5_check
  simpa only [Int.cast_ofNat, Int.cast_pow, Int.cast_one] using h

theorem Y2_3_5_check : checkZ (addL (combZ (41776613 * 2 ^ 24 * 5342931457063200 * 4 ^ 65 * L64 * 5)
    (wts (-2 * 4 ^ 65 * L64 * 5 * 10 ^ 8) 5342931457063200 dv40) [])
    (smulL (-(3 * 2 ^ 24 * 5342931457063200 * 10 ^ 8)) (0 :: logW))) 11 0 0 = true := by
  decide +kernel -- kcost: 11.10 s measured (standalone, profiler type checking); 21 cellOK calls (mirror) of a degree-66 polynomial

/-- `γ = 3/5`, true sup 0.4177661096 (at s = 0.999996). -/
theorem Y2_3_5_leaf : ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv40 (2 ^ 24)) s +
    (3 / 5 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ (41776613 : ℝ) / 10 ^ 8 := by
  have h := leafY (Λ := 5342931457063200) (by norm_num) dv40 dv_div 3 5 41776613 (10 ^ 8) (by norm_num)
    (by norm_num) (by norm_num) Y2_3_5_check
  simpa only [Int.cast_ofNat, Int.cast_pow, Int.cast_one] using h

theorem Y2_4_5_check : checkZ (addL (combZ (52968854 * 2 ^ 24 * 5342931457063200 * 4 ^ 65 * L64 * 5)
    (wts (-2 * 4 ^ 65 * L64 * 5 * 10 ^ 8) 5342931457063200 dv40) [])
    (smulL (-(4 * 2 ^ 24 * 5342931457063200 * 10 ^ 8)) (0 :: logW))) 12 0 0 = true := by
  decide +kernel -- kcost: 12.60 s measured (standalone, profiler type checking); 23 cellOK calls (mirror) of a degree-66 polynomial

/-- `γ = 4/5`, true sup 0.5296885140 (at s = 0.999996). -/
theorem Y2_4_5_leaf : ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv40 (2 ^ 24)) s +
    (4 / 5 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ (52968854 : ℝ) / 10 ^ 8 := by
  have h := leafY (Λ := 5342931457063200) (by norm_num) dv40 dv_div 4 5 52968854 (10 ^ 8) (by norm_num)
    (by norm_num) (by norm_num) Y2_4_5_check
  simpa only [Int.cast_ofNat, Int.cast_pow, Int.cast_one] using h

theorem Y2_1_1_check : checkZ (addL (combZ (64161468 * 2 ^ 24 * 5342931457063200 * 4 ^ 65 * L64 * 1)
    (wts (-2 * 4 ^ 65 * L64 * 1 * 10 ^ 8) 5342931457063200 dv40) [])
    (smulL (-(1 * 2 ^ 24 * 5342931457063200 * 10 ^ 8)) (0 :: logW))) 11 0 0 = true := by
  decide +kernel -- kcost: 11.50 s measured (standalone, profiler type checking); 21 cellOK calls (mirror) of a degree-66 polynomial

/-- `γ = 1/1`, true sup 0.6416146515 (at s = 0.999999). -/
theorem Y2_1_1_leaf : ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv40 (2 ^ 24)) s +
    (1 / 1 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ (64161468 : ℝ) / 10 ^ 8 := by
  have h := leafY (Λ := 5342931457063200) (by norm_num) dv40 dv_div 1 1 64161468 (10 ^ 8) (by norm_num)
    (by norm_num) (by norm_num) Y2_1_1_check
  simpa only [Int.cast_ofNat, Int.cast_pow, Int.cast_one] using h


end

end CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY2b
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY2b.Y2_1_5_leaf
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY2b.Y2_3_10_leaf
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY2b.Y2_2_5_leaf
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY2b.Y2_3_5_leaf
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY2b.Y2_4_5_leaf
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY2b.Y2_1_1_leaf
