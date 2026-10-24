module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX21 : integerGapOK AZX ((-327507 / 2000000 : ℚ),(-313 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketX21 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-327507 / 2000000 : ℚ),(-313 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
