module

public import CatalanMeasure.GenD.Signed.RouteI.ShiftGLeaf

@[expose] public section

/-!
# G5 shiftG, leaf instances: column sups hY, first population

For each knot `γ`: `2 T(dv, s) + γ log (1 + 3 s/4) ≤ Y_γ` on `[0,1]` (`dv = dv24`, scale `2^-24`), `Y_γ` = the true sup rounded up by at least 2e-8 on the 1e-8 grid. The log is replaced by `logW` (degree 65, Mathlib `abs_log_sub_add_sum_range_le`, `log_le_logW`). Each knot is one kernel decision `checkZ` on an integer polynomial built in the kernel.
-/

open Set

namespace CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1b
open CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance CatalanMeasure.GenD.Signed.RouteI.T4Instance
  CatalanMeasure.GenD.Signed.RouteI.ShiftGLeaf OAI.InternalCatalan

noncomputable section

theorem div : divOK 5354228880 24 = true := by decide +kernel

theorem dv_div (k : ℕ) (hk : k < dv24.length) : ((k : ℤ) + 1) ∣ 5354228880 := by
  rw [len_dv24] at hk; exact divOK_spec div hk

theorem Y1_3_10_check : checkZ (addL (combZ (18683771 * 2 ^ 24 * 5354228880 * 4 ^ 65 * L64 * 10)
    (wts (-2 * 4 ^ 65 * L64 * 10 * 10 ^ 8) 5354228880 dv24) [])
    (smulL (-(3 * 2 ^ 24 * 5354228880 * 10 ^ 8)) (0 :: logW))) 15 0 0 = true := by
  decide +kernel -- kcost: 19.80 s measured (standalone, profiler type checking); 41 cellOK calls (mirror) of a degree-66 polynomial

/-- `γ = 3/10`, true sup 0.1868376847 (at s = 0.997725). -/
theorem Y1_3_10_leaf : ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv24 (2 ^ 24)) s +
    (3 / 10 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ (18683771 : ℝ) / 10 ^ 8 := by
  have h := leafY (Λ := 5354228880) (by norm_num) dv24 dv_div 3 10 18683771 (10 ^ 8) (by norm_num)
    (by norm_num) (by norm_num) Y1_3_10_check
  simpa only [Int.cast_ofNat, Int.cast_pow, Int.cast_one] using h

theorem Y1_2_5_check : checkZ (addL (combZ (24277698 * 2 ^ 24 * 5354228880 * 4 ^ 65 * L64 * 5)
    (wts (-2 * 4 ^ 65 * L64 * 5 * 10 ^ 8) 5354228880 dv24) [])
    (smulL (-(2 * 2 ^ 24 * 5354228880 * 10 ^ 8)) (0 :: logW))) 16 0 0 = true := by
  decide +kernel -- kcost: 16.70 s measured (standalone, profiler type checking); 31 cellOK calls (mirror) of a degree-66 polynomial

/-- `γ = 2/5`, true sup 0.2427769557 (at s = 1.000000). -/
theorem Y1_2_5_leaf : ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv24 (2 ^ 24)) s +
    (2 / 5 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ (24277698 : ℝ) / 10 ^ 8 := by
  have h := leafY (Λ := 5354228880) (by norm_num) dv24 dv_div 2 5 24277698 (10 ^ 8) (by norm_num)
    (by norm_num) (by norm_num) Y1_2_5_check
  simpa only [Int.cast_ofNat, Int.cast_pow, Int.cast_one] using h

theorem Y1_3_5_check : checkZ (addL (combZ (35470014 * 2 ^ 24 * 5354228880 * 4 ^ 65 * L64 * 5)
    (wts (-2 * 4 ^ 65 * L64 * 5 * 10 ^ 8) 5354228880 dv24) [])
    (smulL (-(3 * 2 ^ 24 * 5354228880 * 10 ^ 8)) (0 :: logW))) 16 0 0 = true := by
  decide +kernel -- kcost: 16.60 s measured (standalone, profiler type checking); 31 cellOK calls (mirror) of a degree-66 polynomial

/-- `γ = 3/5`, true sup 0.3547001193 (at s = 1.000000). -/
theorem Y1_3_5_leaf : ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv24 (2 ^ 24)) s +
    (3 / 5 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ (35470014 : ℝ) / 10 ^ 8 := by
  have h := leafY (Λ := 5354228880) (by norm_num) dv24 dv_div 3 5 35470014 (10 ^ 8) (by norm_num)
    (by norm_num) (by norm_num) Y1_3_5_check
  simpa only [Int.cast_ofNat, Int.cast_pow, Int.cast_one] using h

theorem Y1_4_5_check : checkZ (addL (combZ (46662331 * 2 ^ 24 * 5354228880 * 4 ^ 65 * L64 * 5)
    (wts (-2 * 4 ^ 65 * L64 * 5 * 10 ^ 8) 5354228880 dv24) [])
    (smulL (-(4 * 2 ^ 24 * 5354228880 * 10 ^ 8)) (0 :: logW))) 16 0 0 = true := by
  decide +kernel -- kcost: 15.90 s measured (standalone, profiler type checking); 31 cellOK calls (mirror) of a degree-66 polynomial

/-- `γ = 4/5`, true sup 0.4666232829 (at s = 1.000000). -/
theorem Y1_4_5_leaf : ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv24 (2 ^ 24)) s +
    (4 / 5 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ (46662331 : ℝ) / 10 ^ 8 := by
  have h := leafY (Λ := 5354228880) (by norm_num) dv24 dv_div 4 5 46662331 (10 ^ 8) (by norm_num)
    (by norm_num) (by norm_num) Y1_4_5_check
  simpa only [Int.cast_ofNat, Int.cast_pow, Int.cast_one] using h

theorem Y1_1_1_check : checkZ (addL (combZ (57854647 * 2 ^ 24 * 5354228880 * 4 ^ 65 * L64 * 1)
    (wts (-2 * 4 ^ 65 * L64 * 1 * 10 ^ 8) 5354228880 dv24) [])
    (smulL (-(1 * 2 ^ 24 * 5354228880 * 10 ^ 8)) (0 :: logW))) 16 0 0 = true := by
  decide +kernel -- kcost: 16.30 s measured (standalone, profiler type checking); 31 cellOK calls (mirror) of a degree-66 polynomial

/-- `γ = 1/1`, true sup 0.5785464465 (at s = 1.000000). -/
theorem Y1_1_1_leaf : ∀ s ∈ Icc (0 : ℝ) 1, 2 * barrierTrialT (trialSeqOf dv24 (2 ^ 24)) s +
    (1 / 1 : ℝ) * Real.log (1 + 3 / 4 * s) ≤ (57854647 : ℝ) / 10 ^ 8 := by
  have h := leafY (Λ := 5354228880) (by norm_num) dv24 dv_div 1 1 57854647 (10 ^ 8) (by norm_num)
    (by norm_num) (by norm_num) Y1_1_1_check
  simpa only [Int.cast_ofNat, Int.cast_pow, Int.cast_one] using h


end

end CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1b
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1b.Y1_3_10_leaf
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1b.Y1_2_5_leaf
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1b.Y1_3_5_leaf
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1b.Y1_4_5_leaf
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafY1b.Y1_1_1_leaf
