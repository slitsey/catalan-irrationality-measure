module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX46 : integerGapOK AZX ((-1433267 / 2000000 : ℚ),(-86 / 125 : ℚ),false)=true :=by decide +kernel
theorem bracketX46 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-1433267 / 2000000 : ℚ),(-86 / 125 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
