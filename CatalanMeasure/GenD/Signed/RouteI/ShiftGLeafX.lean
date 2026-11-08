module

public import CatalanMeasure.GenD.Signed.RouteI.ShiftGLeaf

@[expose] public section

/-!
# G5 shiftG, leaf instances: row sups hX (second and first population)

* `X2_leaf`: `-4 T(du40) - S(dv40) ≤ 1484272/10^8` on `[-1,1]` (second population, K = 40; true sup 0.0148426913).
* `X1_leaf`: `-2 T(du24') - S(dv24) + dl (5/29 - 2x²/(1+x²)) ≤ 2748620/10^8` on `[-1,1]` (first population, K = 24, `du24' = 2 du24/2^24` the increment of the doubled trial, `dl = 213407/2^23`; true sup 0.0274861757).
Each is one kernel decision `checkZ` on an integer polynomial built in the kernel from the trial lists.
-/

open Set

namespace CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafX
open CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance CatalanMeasure.GenD.Signed.RouteI.T4Instance
  CatalanMeasure.GenD.Signed.RouteI.ShiftGLeaf OAI.InternalCatalan

noncomputable section

theorem div40 : divOK 5342931457063200 40 = true := by decide +kernel
theorem div24 : divOK 5354228880 24 = true := by decide +kernel

theorem du40_dv40_div (k : ℕ) (hk : k < du40.length) : ((k : ℤ) + 1) ∣ 5342931457063200 := by
  rw [len_du40] at hk; exact divOK_spec div40 hk
theorem dv40_div (k : ℕ) (hk : k < dv40.length) : ((k : ℤ) + 1) ∣ 5342931457063200 := by
  rw [len_dv40] at hk; exact divOK_spec div40 hk
theorem du24_div (k : ℕ) (hk : k < du24.length) : ((k : ℤ) + 1) ∣ 5354228880 := by
  rw [len_du24] at hk; exact divOK_spec div24 hk
theorem dv24_div (k : ℕ) (hk : k < dv24.length) : ((k : ℤ) + 1) ∣ 5354228880 := by
  rw [len_dv24] at hk; exact divOK_spec div24 hk

theorem X2_check : checkZ (compLin (-1) 2 (combZ (1484272 * 2 ^ 24 * 5342931457063200) (wts (4 * 10 ^ 8) 5342931457063200 du40)
    (wts (10 ^ 8) 5342931457063200 dv40))) 14 0 0 = true := by
  decide +kernel -- kcost: 58.10 s measured (standalone, profiler type checking); 255 cellOK calls (mirror) of a degree-41 integer polynomial

theorem X2_leaf : ∀ x ∈ Icc (-1 : ℝ) 1, -(4 * barrierTrialT (trialSeqOf du40 (2 ^ 24)) x) -
    barrierTrialS (trialSeqOf dv40 (2 ^ 24)) x ≤ (1484272 : ℝ) / 10 ^ 8 := by
  have h := leafX2 (Λ := 5342931457063200) (by norm_num) du40 dv40 du40_dv40_div dv40_div 1484272 X2_check
  simpa only [Int.cast_ofNat] using h

theorem X1_check : checkZ (compLin (-1) 2 (x1Poly 2748620 5354228880 du24 dv24)) 14 0 0 = true := by
  decide +kernel -- kcost: 18.40 s measured (standalone, profiler type checking); 199 cellOK calls (mirror) of a degree-27 integer polynomial

theorem X1_leaf : ∀ x ∈ Icc (-1 : ℝ) 1, -(2 * barrierTrialT (trialSeqOf du24 (2 ^ 23)) x) -
    barrierTrialS (trialSeqOf dv24 (2 ^ 24)) x + (213407 / 2 ^ 23 : ℝ) * (5 / 29 - 2 * x ^ 2 / (1 + x ^ 2)) ≤
      (2748620 : ℝ) / 10 ^ 8 := by
  have h := leafX1 (Λ := 5354228880) (by norm_num) du24 dv24 du24_div dv24_div 2748620 X1_check
  simpa only [Int.cast_ofNat] using h

end

end CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafX
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafX.X2_leaf
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGLeafX.X1_leaf
