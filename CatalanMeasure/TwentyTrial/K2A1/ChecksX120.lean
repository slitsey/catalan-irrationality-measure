module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX120 : integerGapOK AZX ((3669631 / 5000000 : ℚ),(3 / 4 : ℚ),false)=true :=by decide +kernel
theorem bracketX120 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((3669631 / 5000000 : ℚ),(3 / 4 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
