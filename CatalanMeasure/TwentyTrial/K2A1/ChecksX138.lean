module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX138 : integerGapOK AZX ((4695767 / 5000000 : ℚ),(1907 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketX138 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((4695767 / 5000000 : ℚ),(1907 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
