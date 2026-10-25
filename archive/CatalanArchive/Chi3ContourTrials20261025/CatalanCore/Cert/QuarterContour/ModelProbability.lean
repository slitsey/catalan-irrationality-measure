module
public import CatalanCore.Cert.QuarterCompute.Data
public import CatalanCore.Cert.SigmaQuarterContour.PointChecks
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute

/-- The arithmetic model uses the same certified probability witness. -/
theorem probability_mass_sum : ∑ k, QuarterContour.masses pts k = 1 := by
  change ∑ k, QuarterContour.masses SigmaQuarterContour.pts k = 1
  exact SigmaQuarterContour.mass_sum

end CatalanCore.Cert.QuarterCompute
#print axioms CatalanCore.Cert.QuarterCompute.probability_mass_sum
