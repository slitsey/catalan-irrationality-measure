module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX5 : integerGapOK AZX ((-2499827 / 2500000 : ℚ),(-499939 / 500000 : ℚ),false)=true :=by decide +kernel
theorem bracketX5 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-2499827 / 2500000 : ℚ),(-499939 / 500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
