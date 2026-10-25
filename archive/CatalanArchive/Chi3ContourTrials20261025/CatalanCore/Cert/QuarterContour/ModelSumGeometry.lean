module
public import CatalanCore.Cert.QuarterContour.ModelPoint
public import CatalanCore.Cert.QuarterContour.ModelSumFixed
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelSum
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Polynomial
open CatalanCore.Cert.QuarterCompute.ModelFactors
open CatalanCore.Cert.QuarterContour.RealPolynomial
open CatalanCore.Cert.QuarterContour.ModelGeometry

/-- The checked atom geometry discharges the generic polynomial sum's analytic premise. -/
theorem atom_lower_model (S : ℕ) (m : Model.Params) (p : Pt) (j : Jet)
    (hm : Model.validParams m = true) (hj : Model.validJet S m p j = true)
    (v : ℝ) (hv : |v| ≤ 1) :
    atomLower S m v p j ≤ atom p (modelZ m v) := by
  have h := weighted_point_lower S m p j hm hj v hv
  dsimp [atomLower,jetTerm,atom,roundedT]
  dsimp [roundedT] at h
  convert h using 1 <;> ring

/-- Complete centreline model, expressed through the compiler's exact coefficient list. -/
theorem sigma_model (m : Model.Params) (v : ℝ) (ps : List Pt) (js : List Jet)
    (hm : Model.validParams m = true) (hi : Model.inputsOK inputScale m ps js = true)
    (hv : |v| ≤ 1) :
    -(Model.baseSum m ps : ℝ)/2^97+
      evalReal v (allCoeffs factors js)/(denominator : ℝ)-
      (Model.errorSum inputScale js : ℝ)/2^64 ≤
    SigmaP6.Usig ps (modelZ m v).re (modelZ m v).im := by
  exact sigma_lower_of_inputs m v (modelZ m v) ps js hi
    (fun p j hj => atom_lower_model inputScale m p j hm hj v hv)

/-- The final polynomial can be supplied by the packed coefficient decoder. -/
theorem sigma_model_decoded (m : Model.Params) (v : ℝ) (ps : List Pt) (js : List Jet)
    (cs : List ℤ) (hm : Model.validParams m = true)
    (hi : Model.inputsOK inputScale m ps js = true) (hv : |v| ≤ 1)
    (hc : allCoeffs factors js = cs) :
    -(Model.baseSum m ps : ℝ)/2^97+evalReal v cs/(denominator : ℝ)-
      (Model.errorSum inputScale js : ℝ)/2^64 ≤
    SigmaP6.Usig ps (modelZ m v).re (modelZ m v).im := by
  rw [← hc]
  exact sigma_model m v ps js hm hi hv

/-- Extend the decoded polynomial's bound to the fixed horizontal tube. -/
theorem sigma_model_tube (m : Model.Params) (v : ℝ) (ps : List Pt) (js : List Jet)
    (cs : List ℤ) (z : ℂ) (hm : Model.validParams m = true)
    (hi : Model.inputsOK inputScale m ps js = true) (hv : |v| ≤ 1)
    (hc : allCoeffs factors js = cs) (hd : ‖z-modelZ m v‖ ≤ (1/2^30 : ℝ))
    (hprob : ∑ k, QuarterContour.masses ps k = 1) :
    -(Model.baseSum m ps : ℝ)/2^97+evalReal v cs/(denominator : ℝ)-
      (Model.errorSum inputScale js : ℝ)/2^64-((1/2^20 : ℝ)+1/2^39) ≤
    SigmaP6.Usig ps z.re z.im := by
  exact sigma_tube_fixed ps z (modelZ m v) _ hd hprob
    (sigma_model_decoded m v ps js cs hm hi hv hc)
end CatalanCore.Cert.QuarterContour.ModelSum
#print axioms CatalanCore.Cert.QuarterContour.ModelSum.sigma_model_tube