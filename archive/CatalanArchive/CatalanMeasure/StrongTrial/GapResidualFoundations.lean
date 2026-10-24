module
public import CatalanArchive.CatalanMeasure.StrongTrial.GapResidualData
public import CatalanArchive.CatalanMeasure.StrongTrial.Foundations
public import CatalanArchive.CatalanMeasure.Cert.MarkedResidualClosed
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem hcoverRG0 : coverFrom AR [] (-1) planRG0 (-residualGap)=true := by decide +kernel
theorem hcoverRG1 : coverFrom AR [] residualGap planRG1 1=true := by decide +kernel
theorem hendRGLeft : markedResidualEndOK Pc P gapResidualM (-1 : ℚ)=true := by decide +kernel
theorem hendRGLeftGap : markedResidualEndOK Pc P gapResidualM (-401 / 2500 : ℚ)=true := by decide +kernel
theorem hendRGRightGap : markedResidualEndOK Pc P gapResidualM (401 / 2500 : ℚ)=true := by decide +kernel
theorem hendRGRight : markedResidualEndOK Pc P gapResidualM (1 : ℚ)=true := by decide +kernel
end CatalanMeasure.StrongTrial
