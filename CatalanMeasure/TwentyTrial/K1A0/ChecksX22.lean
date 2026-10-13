module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX22 : integerGapOK AZX ((-313 / 2000 : ℚ),(-125019 / 1000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX22 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-313 / 2000 : ℚ),(-125019 / 1000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
