module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX7 : integerGapOK AZX ((-199951 / 200000 : ℚ),(-99951 / 100000 : ℚ),false)=true :=by decide +kernel
theorem bracketX7 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-199951 / 200000 : ℚ),(-99951 / 100000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
