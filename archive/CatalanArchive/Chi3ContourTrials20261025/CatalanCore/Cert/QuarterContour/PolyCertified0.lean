module
public import CatalanCore.Cert.QuarterCompute.PolyModel0
public import CatalanCore.Cert.QuarterContour.PolynomialDecode
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.PolyCertified0
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Polynomial
open CatalanCore.Cert.QuarterContour.PackedPolynomial

/-- The checked jets satisfy the compiler's uniform input budget. -/
lemma jets_bound : ∀ p ∈ PolyModel0.jets,
    p.1.natAbs+p.2.1.natAbs ≤ ModelFactors.inputScale := by
  intro p hp
  exact of_decide_eq_true ((List.all_eq_true.mp PolyModel0.jets_bound) p hp)

/-- The proposed signed coefficient digits lie inside the decoding interval. -/
lemma coefficients_small : Small PolyModel0.radix PolyModel0.coefficients := by
  intro c hc
  have h : 2*(c.natAbs : ℤ) < PolyModel0.radix :=
    of_decide_eq_true ((List.all_eq_true.mp PolyModel0.coefficient_bounds) c hc)
  simpa only [Int.natCast_natAbs] using h

/-- Kernel soundness of the packed checksum: every polynomial coefficient is exact. -/
theorem coefficients_checked : allCoeffs ModelFactors.factors PolyModel0.jets =
    PolyModel0.coefficients := by
  exact coefficients_of_checksum PolyModel0.radix PolyModel0.radix_pos
    ModelFactors.inputScale ModelFactors.factors PolyModel0.jets PolyModel0.coefficients
    PolyModel0.jets_nonempty jets_bound PolyModel0.budget_ok
    PolyModel0.coefficient_length coefficients_small PolyModel0.packed_checked
end CatalanCore.Cert.QuarterContour.PolyCertified0
#print axioms CatalanCore.Cert.QuarterContour.PolyCertified0.coefficients_checked
