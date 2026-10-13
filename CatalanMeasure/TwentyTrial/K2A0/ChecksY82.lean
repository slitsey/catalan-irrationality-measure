module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY82 : integerGapOK AZY ((9961 / 10000 : ℚ),(19961 / 20000 : ℚ),false)=true :=by decide +kernel
theorem bracketY82 : shiftedColumnBracketOK C Vc V AY QY MY ((9961 / 10000 : ℚ),(19961 / 20000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
