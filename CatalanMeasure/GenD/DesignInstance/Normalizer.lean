module

public import CatalanMeasure.GenD.DesignInstance.Kap
public import CatalanMeasure.GenD.Denominator

@[expose] public section

/-!
# D58: the normalizer and the growth of its denominator (instance file)

* `lb`            : the nullity bound `kap = segExp segs - 1`  (`NullityLB`, via `famKap`);
* `Znorm`         : the `Normalizer` of the displaced design (`normalizerOf`);
* `Znorm_growth`  : `log D_N ≤ (gD58 + ε) N²` eventually, with
  `gD58 = (2673/8) log 2 + 116 + 24269/4 - 35369/1848`.
-/

namespace CatalanMeasure.GenD
namespace D58

open PrimeGrowth CatalanMeasure.Parametric Odd Filter

noncomputable section

theorem odd_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p % 2 = 1 :=
  Nat.odd_iff.mp (hp.odd_of_ne_two hp2)

theorem hloss_d58 {N p : ℕ} (hN : 0 < N) (hp : p ≤ Odd.design.H N) :
    (OddProfile.oddLossNat Odd.design N p : ℝ) = N * f58.eval ((p : ℝ) / N) := by
  rw [Odd.design_H] at hp
  unfold OddProfile.oddLossNat
  rw [Odd.design_H]
  by_cases h : 2 * p ≤ 78 * N
  · rw [if_pos h, Odd.lower_eq h]
    exact Odd.lossNat_cast hN hp
  · rw [if_neg h, Odd.upper_eq (by omega) hp]
    exact Odd.lossNat_cast hN hp

theorem hf0_d58 (x : ℝ) (hx : x ≤ 1) : f58.eval x = 116 := by
  simp only [PL.Prof.eval, f58, PL.hinges_cons, PL.hinges_nil]
  rw [PL.ramp_of_le (by linarith : x ≤ 59 / 2), PL.ramp_of_le (by linarith : x ≤ 69 / 2),
    PL.ramp_of_le (by linarith : x ≤ 39), PL.ramp_of_le (by linarith : x ≤ 81 / 2),
    PL.ramp_of_le (by linarith : x ≤ 48), PL.ramp_of_le (by linarith : x ≤ 69),
    PL.ramp_of_le (by linarith : x ≤ 70)]
  ring

/-- The loss integral: `∫_1^78 f58 = 24269/4`. -/
theorem integral_f58 : ∫ x in (1 : ℝ)..78, f58.eval x = 24269 / 4 := by
  rw [PL.Prof.integral_eval f58 (by norm_num)]
  simp only [PL.Prof.area, f58, PL.hingeInt_cons, PL.hingeInt_nil]
  rw [PL.ramp_of_ge (by norm_num : (59 / 2 : ℝ) ≤ 78), PL.ramp_of_ge (by norm_num : (69 / 2 : ℝ) ≤ 78),
    PL.ramp_of_ge (by norm_num : (39 : ℝ) ≤ 78), PL.ramp_of_ge (by norm_num : (81 / 2 : ℝ) ≤ 78),
    PL.ramp_of_ge (by norm_num : (48 : ℝ) ≤ 78), PL.ramp_of_ge (by norm_num : (69 : ℝ) ≤ 78),
    PL.ramp_of_ge (by norm_num : (70 : ℝ) ≤ 78),
    PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 59 / 2), PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 69 / 2),
    PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 39), PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 81 / 2),
    PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 48), PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 69),
    PL.ramp_of_le (by norm_num : (1 : ℝ) ≤ 70)]
  norm_num

/-- Growth constant of the denominator in the design's own unit. -/
def gD58 : ℝ := 2673 / 8 * Real.log 2 + 116 + 24269 / 4 - 35369 / 1848

end

end D58
end CatalanMeasure.GenD
