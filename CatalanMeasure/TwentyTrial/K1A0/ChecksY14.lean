module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY14 : integerGapOK AZY ((2885163 / 10000000 : ℚ),(39 / 125 : ℚ),false)=true :=by decide +kernel
theorem bracketY14 : shiftedColumnBracketOK C Vc V AY QY MY ((2885163 / 10000000 : ℚ),(39 / 125 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
