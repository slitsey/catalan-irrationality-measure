module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX33 : integerGapOK AZX ((47 / 250 : ℚ),(1162691 / 5000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX33 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((47 / 250 : ℚ),(1162691 / 5000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
