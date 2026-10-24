module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX15 : integerGapOK AZX ((-9908971 / 10000000 : ℚ),(-9908969 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX15 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9908971 / 10000000 : ℚ),(-9908969 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
