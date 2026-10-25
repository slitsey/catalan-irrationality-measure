module
public import CatalanCore.Cert.QuarterCompute.PolyModel1
public import CatalanCore.Cert.QuarterContour.PolynomialDecode
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.PolyCertified1
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Polynomial
open CatalanCore.Cert.QuarterContour.PackedPolynomial

/-- The checked jets satisfy the compiler's uniform input budget. -/
lemma jets_bound : ∀ p ∈ PolyModel1.jets,
    p.1.natAbs+p.2.1.natAbs ≤ ModelFactors.inputScale := by
  intro p hp
  exact of_decide_eq_true ((List.all_eq_true.mp PolyModel1.jets_bound) p hp)

/-- The proposed signed coefficient digits lie inside the decoding interval. -/
lemma coefficients_small : Small PolyModel1.radix PolyModel1.coefficients := by
  intro c hc
  have h : 2*(c.natAbs : ℤ) < PolyModel1.radix :=
    of_decide_eq_true ((List.all_eq_true.mp PolyModel1.coefficient_bounds) c hc)
  simpa only [Int.natCast_natAbs] using h

/-- Kernel soundness of the packed checksum: every polynomial coefficient is exact. -/
theorem coefficients_checked : allCoeffs ModelFactors.factors PolyModel1.jets =
    PolyModel1.coefficients := by
  exact coefficients_of_checksum PolyModel1.radix PolyModel1.radix_pos
    ModelFactors.inputScale ModelFactors.factors PolyModel1.jets PolyModel1.coefficients
    PolyModel1.jets_nonempty jets_bound PolyModel1.budget_ok
    PolyModel1.coefficient_length coefficients_small PolyModel1.packed_checked
end CatalanCore.Cert.QuarterContour.PolyCertified1
#print axioms CatalanCore.Cert.QuarterContour.PolyCertified1.coefficients_checked
