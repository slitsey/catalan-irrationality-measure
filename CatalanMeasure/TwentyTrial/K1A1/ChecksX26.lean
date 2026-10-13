module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX26 : integerGapOK AZX ((-1589031 / 5000000 : ℚ),(-39 / 125 : ℚ),false)=true :=by decide +kernel
theorem bracketX26 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-1589031 / 5000000 : ℚ),(-39 / 125 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
