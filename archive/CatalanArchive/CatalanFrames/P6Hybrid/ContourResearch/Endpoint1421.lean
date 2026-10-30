module
public import CatalanCore.Cert.SigmaQuarterContour.DirectCertificate
public import CatalanCore.Cert.SigmaQuarter.Jfun
public import CatalanFrames.P6Hybrid.ContourResearch.MeasureAt
@[expose] public section
namespace CatalanFrames.P6Hybrid.QuarterContour
open CatalanCore
open CatalanCore.Cert.QuarterContour
namespace Endpoint1421
open CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000

/-- Remaining analytic controls are the only input to this endpoint assembly. -/
noncomputable def decayData {segs lines : List Cert.SigmaQuarter.QBox}
    (C : Direct.Controls (-154489/5000000) segs lines)
    (hI : CatalanLambda.Decay.Irho (1/2048 : ℝ) (positions pts) (masses pts) ≤
      (179918953/100000000 : ℝ)) :
    HybridDecayData (Direct.assemble C hI) (1/4) 16 (184428/100000)
      (1485123059/320000000) 3 where
  hα := by norm_num
  hg := by
    intro s
    dsimp only [Direct.assemble,Direct.gQ,Cert.gAlpha]
    push_cast
    norm_num
  hw0 := mass_nonneg pts
  hRc := by norm_num
  hc := radius_le
  hInu := by
    convert Cert.SigmaQuarter.Inu_le using 1 <;> norm_num
  hD := by norm_num [Cert.CertCoreGs.Dof,Direct.assemble]
  hcc := by norm_num [Direct.assemble]

theorem decay_of_controls {segs lines : List Cert.SigmaQuarter.QBox}
    (C : Direct.Controls (-154489/5000000) segs lines)
    (hI : CatalanLambda.Decay.Irho (1/2048 : ℝ) (positions pts) (masses pts) ≤
      (179918953/100000000 : ℝ)) :
    HasDecay family (((1485123059/320000000 : ℚ)) : ℝ) (((376269/50000 : ℚ)) : ℝ) := by
  have h := decay_of_certificate (hsl := by norm_num) (decayData C hI)
  exact h

/-- Conditional until the complete ray, segment and line controls are supplied. -/
theorem measure_of_controls {segs lines : List Cert.SigmaQuarter.QBox}
    (C : Direct.Controls (-154489/5000000) segs lines)
    (hI : CatalanLambda.Decay.Irho (1/2048 : ℝ) (positions pts) (masses pts) ≤
      (179918953/100000000 : ℝ)) :
    Measure.MeasureLBAt CatalanFrames.P6.chi3L2 (((1421/100 : ℚ)) : ℝ) := by
  exact chi3_measure_of_decay (D := 1485123059/320000000) (c := 376269/50000)
    (E := 1421/100) (by norm_num) (decay_of_controls C hI)
    (by norm_num) (by norm_num) (by norm_num) Direct.final_ratio

end Endpoint1421
end CatalanFrames.P6Hybrid.QuarterContour
#print axioms CatalanFrames.P6Hybrid.QuarterContour.Endpoint1421.measure_of_controls
