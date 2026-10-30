module

public import CatalanMeasure.GenD.TwoAdic
public import CatalanMeasure.GenD.D58.OddProfile

@[expose] public section

/-!
# 2-adic constant of the design (58,9,3,5,3) (instance file)

`a2 = ((58 + 78 - 9)^2/8 - 58^2/2) / 58^2 = 2673/26912`, i.e. `A2 = 2673/8 N²`.
-/

namespace CatalanMeasure.GenD
namespace D58
namespace TwoAdicInst

open CatalanMeasure.Parametric OAI.InternalCatalan Filter
open scoped Topology

noncomputable section

theorem a2_design : TwoAdic.a2 Odd.design = 2673 / 26912 := by
  have hH : Odd.design.H 1 = 78 := by simpa using Odd.design_H 1
  unfold TwoAdic.a2 TwoAdic.A2
  rw [hH]
  simp only [Odd.design]
  norm_num

/-- `v_2(det) ≥ -(2673/26912 + ε) (58 N)²` eventually. -/
theorem two_adic_eventually_lower (z : ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, determinantRat Odd.design z N ≠ 0 →
      -(2673 / 26912 : ℝ) - ε ≤
        (padicValRat 2 (determinantRat Odd.design z N) : ℝ) / (58 * (N : ℝ)) ^ 2 := by
  have h := TwoAdic.determinantRat_two_adic_eventually_lower Odd.design Odd.design_admissible z hε
  filter_upwards [h] with N hN hd
  have := hN hd
  rw [a2_design] at this
  have hn : (Odd.design.n N : ℝ) = 58 * (N : ℝ) := by
    simp [Parameters.n, Odd.design]
  rwa [hn] at this

end
end TwoAdicInst
end D58
end CatalanMeasure.GenD
