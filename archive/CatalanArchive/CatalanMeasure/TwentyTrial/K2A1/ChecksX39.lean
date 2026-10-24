module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX39 : integerGapOK AZX ((-1008459 / 1250000 : ℚ),(-8067669 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX39 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-1008459 / 1250000 : ℚ),(-8067669 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
