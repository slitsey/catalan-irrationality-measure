module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY24 : integerGapOK AZY ((1 / 2 : ℚ),(1396279 / 2500000 : ℚ),false)=true :=by decide +kernel
theorem bracketY24 : shiftedColumnBracketOK C Vc V AY QY MY ((1 / 2 : ℚ),(1396279 / 2500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
