module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX51 : integerGapOK AZX ((39 / 125 : ℚ),(1724889 / 5000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX51 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((39 / 125 : ℚ),(1724889 / 5000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
