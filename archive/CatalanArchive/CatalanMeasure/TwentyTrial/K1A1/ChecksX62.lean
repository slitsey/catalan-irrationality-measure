module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX62 : integerGapOK AZX ((5155623 / 10000000 : ℚ),(281 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketX62 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((5155623 / 10000000 : ℚ),(281 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
