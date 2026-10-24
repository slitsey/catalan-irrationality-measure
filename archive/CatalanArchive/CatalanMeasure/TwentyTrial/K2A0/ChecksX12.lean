module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX12 : integerGapOK AZX ((-995931 / 1000000 : ℚ),(-2489827 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX12 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-995931 / 1000000 : ℚ),(-2489827 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
