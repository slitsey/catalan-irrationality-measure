module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX108 : integerGapOK AZX ((5311107 / 10000000 : ℚ),(281 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketX108 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((5311107 / 10000000 : ℚ),(281 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
