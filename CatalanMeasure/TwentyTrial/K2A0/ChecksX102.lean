module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX102 : integerGapOK AZX ((526101 / 1250000 : ℚ),(219 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketX102 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((526101 / 1250000 : ℚ),(219 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
