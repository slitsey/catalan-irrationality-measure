module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX68 : integerGapOK AZX ((-39 / 125 : ℚ),(-657031 / 2500000 : ℚ),false)=true :=by decide +kernel
theorem bracketX68 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-39 / 125 : ℚ),(-657031 / 2500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
