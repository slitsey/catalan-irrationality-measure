module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX20 : integerGapOK AZX ((-1006897 / 2500000 : ℚ),(-3 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketX20 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-1006897 / 2500000 : ℚ),(-3 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
