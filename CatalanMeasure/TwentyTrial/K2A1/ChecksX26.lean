module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX26 : integerGapOK AZX ((-469 / 500 : ℚ),(-9360087 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX26 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-469 / 500 : ℚ),(-9360087 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
