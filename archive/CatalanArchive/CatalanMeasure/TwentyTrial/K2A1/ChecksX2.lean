module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX2 : integerGapOK AZX ((-4999917 / 5000000 : ℚ),(-499939 / 500000 : ℚ),false)=true :=by decide +kernel
theorem bracketX2 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-4999917 / 5000000 : ℚ),(-499939 / 500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
