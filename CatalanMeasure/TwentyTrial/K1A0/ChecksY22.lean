module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY22 : integerGapOK AZY ((4854623 / 10000000 : ℚ),(2427313 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY22 : shiftedColumnBracketOK C Vc V AY QY MY ((4854623 / 10000000 : ℚ),(2427313 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
