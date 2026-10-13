module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY19 : integerGapOK AZY ((2122463 / 5000000 : ℚ),(66327 / 156250 : ℚ),true)=true :=by decide +kernel
theorem bracketY19 : shiftedColumnBracketOK C Vc V AY QY MY ((2122463 / 5000000 : ℚ),(66327 / 156250 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
