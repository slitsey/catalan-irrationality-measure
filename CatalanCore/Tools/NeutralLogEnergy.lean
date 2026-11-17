module

public import CatalanCore.Zeta5.Energy.ZeroMass

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace CatalanCore.Tools

/-- Sign adapter from the existing zero-mass logarithmic energy inequality. -/
theorem neutral_log_energy_nonneg {ι : Type*} [Fintype ι]
    {m : ι → Measure ℂ} [∀ k, IsFiniteMeasure (m k)] {s : ι → ℝ} {R : ℝ}
    (hR : ∀ k, ∀ᵐ z ∂(m k), ‖z‖ ≤ R)
    (hmass : ∑ k, s k * (m k).real univ = 0)
    (hint : ∀ k l, Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((m k).prod (m l)))
    (hae : ∀ k l, ∀ᵐ p ∂((m k).prod (m l)), p.1 ≠ p.2) :
    0 ≤ -CatalanCore.Zeta5.Energy.energy s m (fun z w => Real.log ‖z - w‖) := by
  exact neg_nonneg.mpr (CatalanCore.Zeta5.Energy.energy_log_nonpos hR hmass hint hae)

end CatalanCore.Tools

#print axioms CatalanCore.Tools.neutral_log_energy_nonneg
