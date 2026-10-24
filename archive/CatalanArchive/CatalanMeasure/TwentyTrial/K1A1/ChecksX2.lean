module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX2 : integerGapOK AZX ((-9999823 / 10000000 : ℚ),(-999939 / 1000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX2 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9999823 / 10000000 : ℚ),(-999939 / 1000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
