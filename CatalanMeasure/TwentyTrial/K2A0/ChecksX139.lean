module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX139 : integerGapOK AZX ((469 / 500 : ℚ),(383177 / 400000 : ℚ),false)=true :=by decide +kernel
theorem bracketX139 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((469 / 500 : ℚ),(383177 / 400000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
