module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX8 : integerGapOK AZX ((-4994691 / 5000000 : ℚ),(-499469 / 500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX8 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-4994691 / 5000000 : ℚ),(-499469 / 500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
