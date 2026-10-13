module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY66 : integerGapOK AZY ((4981671 / 5000000 : ℚ),(19961 / 20000 : ℚ),false)=true :=by decide +kernel
theorem bracketY66 : shiftedColumnBracketOK C Vc V AY QY MY ((4981671 / 5000000 : ℚ),(19961 / 20000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
