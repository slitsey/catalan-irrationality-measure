module
public import CatalanCore.Cert.SigmaQuarterContour.ControlsBridge
public import CatalanCore.Cert.QuarterContour.RawRay
public import CatalanCore.Cert.SigmaQuarterContour.SegmentAssembly
public import CatalanCore.Cert.QuarterContour.LineAssembly
public import CatalanCore.Cert.QuarterContour.EnergyExact
public import CatalanFrames.P6Hybrid.ContourResearch.Endpoint1421
@[expose] public section
namespace CatalanFrames.P6Hybrid.QuarterContour.Cert1421
open CatalanCore
open CatalanCore.Cert.QuarterContour
open CatalanCore.Cert.SigmaQuarterContour

/-- All finite contour obligations, supplied by their independently checked branches. -/
theorem controls : Direct.Controls (-154489/5000000) SegmentFinite.cells LineAssembly.cells :=
  ControlsBridge.of_bounds (-154489/5000000) SegmentFinite.cells LineAssembly.cells
    RawRay.ray_bound SegmentFinite.shape SegmentFinite.cover SegmentFinite.scost
    (SegmentAssembly.sound (1/100000)) LineAssembly.line_sound LineAssembly.line_cover

/-- The complete local quarter certificate at14.21. -/
theorem chi3_measure : Measure.MeasureLBAt CatalanFrames.P6.chi3L2 (((1421/100 : ℚ)) : ℝ) :=
  Endpoint1421.measure_of_controls controls EnergyExact.energy_le_rounded

end CatalanFrames.P6Hybrid.QuarterContour.Cert1421
#print axioms CatalanFrames.P6Hybrid.QuarterContour.Cert1421.chi3_measure
