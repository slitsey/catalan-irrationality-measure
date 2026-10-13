module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY63 : integerGapOK AZY ((4961 / 5000 : ℚ),(9961 / 10000 : ℚ),false)=true :=by decide +kernel
theorem bracketY63 : shiftedColumnBracketOK C Vc V AY QY MY ((4961 / 5000 : ℚ),(9961 / 10000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
