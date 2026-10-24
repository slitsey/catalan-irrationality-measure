module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX41 : integerGapOK AZX ((124889 / 1000000 : ℚ),(1 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketX41 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((124889 / 1000000 : ℚ),(1 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
