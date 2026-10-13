module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX60 : integerGapOK AZX ((-35911 / 80000 : ℚ),(-4488873 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX60 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-35911 / 80000 : ℚ),(-4488873 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
