module
public import CatalanCore.Cert.QuarterContour.ModelSum
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelSum
open CatalanCore.Cert.QuarterCompute

theorem sigma_tube_fixed (ps : List Pt) (z z0 : ℂ) (L : ℝ)
    (hd : ‖z-z0‖ ≤ (1/2^30 : ℝ))
    (hprob : ∑ k, QuarterContour.masses ps k = 1)
    (hL : L ≤ SigmaP6.Usig ps z0.re z0.im) :
    L-((1/2^20 : ℝ)+1/2^39) ≤ SigmaP6.Usig ps z.re z.im := by
  have h := sigma_tube_lower ps z z0 (1/2^30 : ℝ) L (by positivity) hd hprob hL
  have he : (((1/2^30 : ℝ)/(1/2048)+((1/2^30 : ℝ)/(1/2048))^2)/2) =
      (1/2^20 : ℝ)+1/2^39 := by norm_num
  rw [he] at h
  exact h

theorem sigma_tube_fixed_integer (ps : List Pt) (z z0 : ℂ) (L : ℝ)
    (hd : ‖z-z0‖ ≤ (1/2^30 : ℝ))
    (hprob : ∑ k, QuarterContour.masses ps k = 1)
    (hL : L ≤ SigmaP6.Usig ps z0.re z0.im) :
    L-(268435968 : ℝ)/2^48 ≤ SigmaP6.Usig ps z.re z.im := by
  have h := sigma_tube_fixed ps z z0 L hd hprob hL
  have he : (1/2^20 : ℝ)+1/2^39 = (268435968 : ℝ)/2^48 := by norm_num
  rw [he] at h
  exact h
end CatalanCore.Cert.QuarterContour.ModelSum
#print axioms CatalanCore.Cert.QuarterContour.ModelSum.sigma_tube_fixed