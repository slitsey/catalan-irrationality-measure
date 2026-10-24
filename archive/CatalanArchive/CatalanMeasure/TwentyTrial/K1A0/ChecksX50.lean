module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX50 : integerGapOK AZX ((129081 / 250000 : ℚ),(281 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketX50 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((129081 / 250000 : ℚ),(281 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
