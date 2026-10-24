module
public import CatalanArchive.CatalanMeasure.StrongTrial.GapResidualFoundations
public import CatalanArchive.CatalanMeasure.StrongTrial.Foundations
public import CatalanArchive.CatalanMeasure.Cert.MarkedResidualClosed
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketRG1_14 : markedResidualClosedBracketOK Pc P AR QR gapResidualM ((999999997619 / 1000000000000 : ℚ),(499999998811 / 500000000000 : ℚ),true)=true := by decide +kernel
theorem bracketRG1_16 : markedResidualClosedBracketOK Pc P AR QR gapResidualM ((999999999837 / 1000000000000 : ℚ),(6249999999 / 6250000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
