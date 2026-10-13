module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX144 : integerGapOK AZX ((9709931 / 10000000 : ℚ),(1221 / 1250 : ℚ),false)=true :=by decide +kernel
theorem bracketX144 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((9709931 / 10000000 : ℚ),(1221 / 1250 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
