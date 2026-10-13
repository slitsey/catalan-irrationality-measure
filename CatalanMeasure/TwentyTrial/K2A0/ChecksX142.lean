module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX142 : integerGapOK AZX ((969 / 1000 : ℚ),(1213741 / 1250000 : ℚ),false)=true :=by decide +kernel
theorem bracketX142 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((969 / 1000 : ℚ),(1213741 / 1250000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
