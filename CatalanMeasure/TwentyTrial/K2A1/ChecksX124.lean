module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX124 : integerGapOK AZX ((203 / 250 : ℚ),(8179009 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX124 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((203 / 250 : ℚ),(8179009 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
