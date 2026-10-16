module
public import CatalanMeasure.StrongTrial.GapResidualFoundations
public import CatalanMeasure.StrongTrial.Foundations
public import CatalanMeasure.Cert.MarkedResidualClosed
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketRG1_2 : markedResidualClosedBracketOK Pc P AR QR gapResidualM ((897061069521 / 1000000000000 : ℚ),(224265267381 / 250000000000 : ℚ),true)=true := by decide +kernel
theorem bracketRG1_8 : markedResidualClosedBracketOK Pc P AR QR gapResidualM ((499999053041 / 500000000000 : ℚ),(199999621217 / 200000000000 : ℚ),true)=true := by decide +kernel
theorem bracketRG1_10 : markedResidualClosedBracketOK Pc P AR QR gapResidualM ((999999723981 / 1000000000000 : ℚ),(62499982749 / 62500000000 : ℚ),true)=true := by decide +kernel
theorem bracketRG1_12 : markedResidualClosedBracketOK Pc P AR QR gapResidualM ((999999974091 / 1000000000000 : ℚ),(499999987047 / 500000000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
