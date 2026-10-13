module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX52 : integerGapOK AZX ((1724889 / 5000000 : ℚ),(172489 / 500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX52 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1724889 / 5000000 : ℚ),(172489 / 500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
