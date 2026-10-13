module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX41 : integerGapOK AZX ((869197 / 2500000 : ℚ),(3 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketX41 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((869197 / 2500000 : ℚ),(3 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
