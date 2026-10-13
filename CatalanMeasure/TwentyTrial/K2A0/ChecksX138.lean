module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX138 : integerGapOK AZX ((1171021 / 1250000 : ℚ),(469 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketX138 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1171021 / 1250000 : ℚ),(469 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
