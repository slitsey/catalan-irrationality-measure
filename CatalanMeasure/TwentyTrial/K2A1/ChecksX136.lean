module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX136 : integerGapOK AZX ((469 / 500 : ℚ),(2347883 / 2500000 : ℚ),false)=true :=by decide +kernel
theorem bracketX136 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((469 / 500 : ℚ),(2347883 / 2500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
