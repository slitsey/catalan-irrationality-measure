module

public import CatalanMeasure.GenD.D58.SecondTrial590
public import CatalanMeasure.GenD.D58.Circle
public import CatalanMeasure.GenD.D58.FirstTrialCert

@[expose] public section

/-!
# D58 = (58,9,3,5,3), bank K590: the irrationality measure bound `μ(G) ≤ 590`, hypothesis-free

Assembles the K590 second-population certificate (`SecondTrial590`), the gap-circle certificate
(`Circle`) and the first-population certificate (`FirstTrialCert`).
-/

namespace CatalanMeasure.GenD
namespace D58
open Filter Set

theorem near_sup_d58_590 : ∀ y ∈ Ioo (0 : ℝ) 1,
    -Analytic.gRes Odd.design * Real.log (1 + y ^ 2) +
      (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) * Real.log y -
        secondU590 1 * y ≤ nearCap := by
  intro y hy
  have h := second_near_sup_d58_590 y hy
  rw [Analytic.Instances.d58_gRes]
  have e : (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) = 47 / 58 := by
    norm_num [Odd.design]
  rw [e]
  unfold nearCap
  have e2 : (-77 / 100 : ℝ) = -(77 / 100) := by norm_num
  rw [e2]
  exact h

/-- `μ(G) ≤ 590` for the design `(58,9,3,5,3)`. -/
theorem catalan_irrationalityMeasure_590 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(590 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  measure_590_second_population_K590 (rc := 1001 / 1000) (C := 3) (wc := 52788 / 1000)
    circ_hr1 circ_hr2 circ_hcirc circ_hwc590 K590.firstTrialCert near_sup_d58_590

#print axioms catalan_irrationalityMeasure_590

end D58
end CatalanMeasure.GenD
