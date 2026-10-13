module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX65 : integerGapOK AZX ((7292919 / 10000000 : ℚ),(3 / 4 : ℚ),false)=true :=by decide +kernel
theorem bracketX65 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((7292919 / 10000000 : ℚ),(3 / 4 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
