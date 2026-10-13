module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX78 : integerGapOK AZX ((3 / 4 : ℚ),(1 : ℚ),false)=true :=by decide +kernel
theorem bracketX78 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((3 / 4 : ℚ),(1 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
