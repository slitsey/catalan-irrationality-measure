module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX19 : integerGapOK AZX ((-2464119 / 2500000 : ℚ),(-1969 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketX19 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-2464119 / 2500000 : ℚ),(-1969 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
