module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX8 : integerGapOK AZX ((-99951 / 100000 : ℚ),(-49951 / 50000 : ℚ),false)=true :=by decide +kernel
theorem bracketX8 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-99951 / 100000 : ℚ),(-49951 / 50000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
