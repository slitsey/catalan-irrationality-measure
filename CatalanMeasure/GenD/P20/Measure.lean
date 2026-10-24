module

public import CatalanMeasure.GenD.Final
public import CatalanMeasure.GenD.Nonvanishing
public import CatalanMeasure.GenD.P20.Normalizer
public import CatalanMeasure.GenD.P20.Budget
public import CatalanMeasure.GenD.P20.Circle
public import CatalanMeasure.GenD.P20.FirstTrial
public import CatalanMeasure.GenD.P20.SecondTrial
public import CatalanMeasure.Parametric.TwentyBase.Nonvanishing
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# P20: `μ(G) ≤ 728` as `measure_of_design` (instance assembly)

`measure_of_design twenty` with the payments of `P20.Budget` (window parameter `w = 1`), the
normalizer `Znorm`, the circle, first-trial and second-trial certificates, and the C3 certificate
`TwentyBase.twenty_base_residue_dets` (three residue determinants modulo 1009).
-/

namespace CatalanMeasure.GenD
namespace P20
open Polynomial Filter Real CatalanMeasure.Parametric OAI.InternalCatalan Set
open scoped Topology
noncomputable section

instance fact1009 : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

theorem nonvanishing_p20 :
    ∃ N1 : ℕ, ∀ p : ℕ, N1 ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
      aeval ((a : ℝ) / b) (Parametric.deltaPoly design p) ≠ 0 :=
  nonvanishing_of_c3 design design_admissible (by norm_num)
    (by rw [design_H]; norm_num)
    TwentyBase.twenty_base_residue_dets.1 TwentyBase.twenty_base_residue_dets.2.1
    TwentyBase.twenty_base_residue_dets.2.2

theorem delta_small_p20 (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(rho * (N : ℝ))) →
        |aeval x (Parametric.deltaPoly design N)| ≤
          Real.exp (-((tDelta - ε) * (N : ℝ) ^ 2)) :=
  Analytic.delta_small_of_certificates design_admissible (g := 401 / 2500) circ_hg0 circ_hg1
    circ_ha4 circ_hr1 circ_hr2 circ_hcirc (w := rho - 20 * secondCost) circ_hwc
    (F := firstTrial) (S := secondCert)
    (r := 20 * secondCost) (by norm_num [design, Parametric.twenty, firstCost, secondCost])
    (by norm_num [design, Parametric.twenty]) (by linarith)
    (by
      unfold tDelta
      rw [show ((design.n0 : ℕ) : ℝ) = 20 by norm_num [design, Parametric.twenty]]
      ring) ε hε

/-- **`μ(G) ≤ 728`** as `measure_of_design` for `(20, 3, 1, 2, 1)`. -/
theorem measure_728 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(728 : ℝ)) < |catalan - (a : ℝ) / b| := by
  have h := measure_of_design design
    { B := 728, Z := Znorm, w := 1, ρ := rho, η := eta, κ := kappa, δ := delta,
      pay := by rw [n0_sub_g0]; simpa using pay,
      gD := gD20, D_growth := fun ε hε => Znorm_growth hε, tΔ := tDelta,
      delta_small := delta_small_p20, eta_le := eta_le, nonvanishing := nonvanishing_p20 }
  simpa using h

#print axioms measure_728

end
end P20
end CatalanMeasure.GenD
