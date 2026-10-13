module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX9 : integerGapOK AZX ((-49951 / 50000 : ℚ),(-19961 / 20000 : ℚ),false)=true :=by decide +kernel
theorem bracketX9 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-49951 / 50000 : ℚ),(-19961 / 20000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
