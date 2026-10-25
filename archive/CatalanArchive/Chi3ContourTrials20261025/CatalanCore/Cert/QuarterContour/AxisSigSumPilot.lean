module
public import CatalanCore.Cert.SigmaQuarterContour.Data
public import CatalanCore.Cert.QuarterContour.AxisSigSum
public import CatalanCore.Cert.QuarterContour.RawMacroNums
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.AxisSigSumPilot
open CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def sample : Macro := raw_macro% [965868519424,0,0,2950,0,0,0,0,0,0,964438261760,964455038976,0,0,642958841173,642970025984,-6207511901,0]
set_option profiler true in
theorem baseline_checked : FastMacros.axisOK SigmaQuarterContour.pts sample = true := by decide +kernel
set_option profiler true in
theorem folded_checked : AxisSigSum.axisOK SigmaQuarterContour.pts sample = true := by decide +kernel
theorem old_checked : SigmaQuarter.axisOK SigmaQuarterContour.pts sample = true := by
  rw [← AxisSigSum.axisOK_eq]
  exact folded_checked
end CatalanCore.Cert.QuarterContour.AxisSigSumPilot
#print axioms CatalanCore.Cert.QuarterContour.AxisSigSumPilot.baseline_checked
#print axioms CatalanCore.Cert.QuarterContour.AxisSigSumPilot.folded_checked
#print axioms CatalanCore.Cert.QuarterContour.AxisSigSumPilot.old_checked
