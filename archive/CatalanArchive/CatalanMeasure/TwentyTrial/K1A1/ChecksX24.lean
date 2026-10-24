module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX24 : integerGapOK AZX ((-687 / 2000 : ℚ),(-198629 / 625000 : ℚ),false)=true :=by decide +kernel
theorem bracketX24 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-687 / 2000 : ℚ),(-198629 / 625000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
