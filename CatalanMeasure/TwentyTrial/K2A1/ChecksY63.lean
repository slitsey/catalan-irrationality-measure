module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY63 : integerGapOK AZY ((1813 / 2000 : ℚ),(373019 / 400000 : ℚ),false)=true :=by decide +kernel
theorem bracketY63 : shiftedColumnBracketOK C Vc V AY QY MY ((1813 / 2000 : ℚ),(373019 / 400000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
