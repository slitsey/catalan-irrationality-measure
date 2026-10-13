module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX129 : integerGapOK AZX ((2141261 / 2500000 : ℚ),(7 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketX129 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((2141261 / 2500000 : ℚ),(7 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
