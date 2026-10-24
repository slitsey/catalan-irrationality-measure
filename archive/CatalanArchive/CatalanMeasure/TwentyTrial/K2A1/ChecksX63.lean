module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX63 : integerGapOK AZX ((-3860027 / 10000000 : ℚ),(-154401 / 400000 : ℚ),true)=true :=by decide +kernel
theorem bracketX63 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-3860027 / 10000000 : ℚ),(-154401 / 400000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
