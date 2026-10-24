module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX63 : integerGapOK AZX ((-463579 / 1250000 : ℚ),(-370863 / 1000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX63 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-463579 / 1250000 : ℚ),(-370863 / 1000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
