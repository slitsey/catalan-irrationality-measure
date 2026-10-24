module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX44 : integerGapOK AZX ((806393 / 2000000 : ℚ),(219 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketX44 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((806393 / 2000000 : ℚ),(219 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
