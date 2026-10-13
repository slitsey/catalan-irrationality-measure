module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX42 : integerGapOK AZX ((3 / 8 : ℚ),(4031963 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX42 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((3 / 8 : ℚ),(4031963 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
