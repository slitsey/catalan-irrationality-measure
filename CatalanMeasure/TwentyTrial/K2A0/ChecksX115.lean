module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX115 : integerGapOK AZX ((1313 / 2000 : ℚ),(1716511 / 2500000 : ℚ),false)=true :=by decide +kernel
theorem bracketX115 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1313 / 2000 : ℚ),(1716511 / 2500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
