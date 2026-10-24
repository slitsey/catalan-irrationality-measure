module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX66 : integerGapOK AZX ((-3351139 / 10000000 : ℚ),(-104723 / 312500 : ℚ),true)=true :=by decide +kernel
theorem bracketX66 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-3351139 / 10000000 : ℚ),(-104723 / 312500 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
