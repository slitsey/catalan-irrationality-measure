module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX26 : integerGapOK AZX ((0 : ℚ),(1 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketX26 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((0 : ℚ),(1 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
