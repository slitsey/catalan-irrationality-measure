module

public import CatalanMeasure.GenD.Analytic.GapCircleGen
public import CatalanMeasure.GenD.P20.Budget
public import CatalanMeasure.GapCircle.Bound

@[expose] public section

/-!
# P20: the circle certificate `GapCircleBound` (instance file)

The existing P20 gap-circle certificate (`GapCircle.Bound`, 55 piece checks, cover constant
`gapWeightCost = 17.913`) fed into the generic `GapCircleBound twenty` of `GapCircleGen`
(the nodes `gapNodes a N` of the old files are `gapNodesGen a (18 N)`, `gapPolyK a (9 N)` is
`gapPolynomial a N`, definitionally).  Gap `g = 401/2500`, radius `1001/1000`, `C = 1`.
-/

namespace CatalanMeasure.GenD
namespace P20

open CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric

noncomputable section

theorem gapCircleBound_p20 :
    GapCircleBound design (interpolationGap : ℝ) (1001 / 1000) 1 gapWeightCost := by
  intro N z hN hz
  have hK : (((design.n0 - design.g0) * N) + 1) / 2 = 9 * N := by
    change ((20 - 2) * N + 1) / 2 = 9 * N
    omega
  rw [hK, show gapPolyK (interpolationGap : ℝ) (9 * N) = gapPolynomial (interpolationGap : ℝ) N from rfl,
    one_mul]
  have := GapCircle.circle_bound N z hz
  have e : design.h N + design.q N = 2 * N := by
    simp only [Parameters.h, Parameters.q, design, twenty]; ring
  rw [e]
  simpa using this

theorem circ_hg0 : (0 : ℝ) < 401 / 2500 := by norm_num
theorem circ_hg1 : (401 / 2500 : ℝ) < 1 := by norm_num
theorem circ_ha4 : 1 - (2 * (401 / 2500 : ℝ) / (1 + (401 / 2500 : ℝ) ^ 2)) ^ 2 ≤
    4 * (2 * (401 / 2500 : ℝ) / (1 + (401 / 2500 : ℝ) ^ 2)) := by norm_num
theorem circ_hr1 : (1 : ℝ) < 1001 / 1000 := by norm_num
theorem circ_hr2 : (1001 / 1000 : ℝ) ≤ 2 := by norm_num

theorem circ_hcirc :
    GapCircleBound design (2 * (401 / 2500 : ℝ) / (1 + (401 / 2500 : ℝ) ^ 2))
      (1001 / 1000) 1 gapWeightCost := by
  have e : (2 * (401 / 2500 : ℝ) / (1 + (401 / 2500 : ℝ) ^ 2)) = (interpolationGap : ℝ) := by
    norm_num [interpolationGap]
  rw [e]
  exact gapCircleBound_p20

theorem circ_hwc : gapWeightCost < rho - 20 * secondCost := by
  norm_num [gapWeightCost, rho, secondCost, wcap]

end
end P20
end CatalanMeasure.GenD
