module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX7 : integerGapOK AZX ((-49951 / 50000 : ℚ),(-4994691 / 5000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX7 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-49951 / 50000 : ℚ),(-4994691 / 5000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
