module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX23 : integerGapOK AZX ((-125019 / 1000000 : ℚ),(-312547 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX23 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-125019 / 1000000 : ℚ),(-312547 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
