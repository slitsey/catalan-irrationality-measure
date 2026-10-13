module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX32 : integerGapOK AZX ((-2201393 / 10000000 : ℚ),(-47 / 250 : ℚ),false)=true :=by decide +kernel
theorem bracketX32 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-2201393 / 10000000 : ℚ),(-47 / 250 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
