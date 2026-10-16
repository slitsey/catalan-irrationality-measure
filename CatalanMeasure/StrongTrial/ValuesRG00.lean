module
public import CatalanMeasure.StrongTrial.GapResidualFoundations
public import CatalanMeasure.StrongTrial.Foundations
public import CatalanMeasure.Cert.MarkedResidualClosed
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketRG0_1 : markedResidualClosedBracketOK Pc P AR QR gapResidualM ((-999999801557 / 1000000000000 : ℚ),(-499999900777 / 500000000000 : ℚ),true)=true := by decide +kernel
theorem bracketRG0_9 : markedResidualClosedBracketOK Pc P AR QR gapResidualM ((-534567041019 / 1000000000000 : ℚ),(-66820880127 / 125000000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
