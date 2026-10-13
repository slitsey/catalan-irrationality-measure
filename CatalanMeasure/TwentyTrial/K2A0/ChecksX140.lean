module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX140 : integerGapOK AZX ((383177 / 400000 : ℚ),(2394857 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX140 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((383177 / 400000 : ℚ),(2394857 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
