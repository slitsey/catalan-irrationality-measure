module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX31 : integerGapOK AZX ((-4459767 / 5000000 : ℚ),(-7 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketX31 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-4459767 / 5000000 : ℚ),(-7 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
