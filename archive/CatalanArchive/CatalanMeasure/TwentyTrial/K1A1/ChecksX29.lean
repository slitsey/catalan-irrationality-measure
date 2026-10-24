module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX29 : integerGapOK AZX ((-133763 / 500000 : ℚ),(-1 / 4 : ℚ),false)=true :=by decide +kernel
theorem bracketX29 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-133763 / 500000 : ℚ),(-1 / 4 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
