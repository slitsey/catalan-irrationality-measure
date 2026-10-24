module

public import CatalanMeasure.GenD.D58.SecondTrial
public import CatalanMeasure.GenD.D58.Circle
public import CatalanMeasure.GenD.D58.FirstTrialCert

@[expose] public section

/-!
# D58 = (58,9,3,5,3): the irrationality measure bound `μ(G) ≤ 592`, hypothesis-free

Assembles the second-population certificate (`SecondTrial`), the gap-circle certificate (`Circle`)
and the first-population certificate (`FirstTrialCert`) in `measure_592_second_population`.
-/

namespace CatalanMeasure.GenD
namespace D58
open Filter Set

theorem near_sup_d58 : ∀ y ∈ Ioo (0 : ℝ) 1,
    -Analytic.gRes Odd.design * Real.log (1 + y ^ 2) +
      (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) * Real.log y -
        secondU 1 * y ≤ nearCap := by
  intro y hy
  have h := second_near_sup_d58 y hy
  rw [Analytic.Instances.d58_gRes]
  have e : (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) = 47 / 58 := by
    norm_num [Odd.design]
  rw [e]
  unfold nearCap
  have e2 : (-77 / 100 : ℝ) = -(77 / 100) := by norm_num
  rw [e2]
  exact h

/-- `μ(G) ≤ 592` for the design `(58,9,3,5,3)`. -/
theorem catalan_irrationalityMeasure_592 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(592 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  measure_592_second_population (rc := 1001 / 1000) (C := 3) (wc := 52788 / 1000)
    circ_hr1 circ_hr2 circ_hcirc circ_hwc160 K160.firstTrialCert near_sup_d58

#print axioms catalan_irrationalityMeasure_592

end D58
end CatalanMeasure.GenD
