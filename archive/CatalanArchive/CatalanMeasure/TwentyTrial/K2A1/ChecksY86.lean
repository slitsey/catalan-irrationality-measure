module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY86 : integerGapOK AZY ((9991451 / 10000000 : ℚ),(9991453 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY86 : shiftedColumnBracketOK C Vc V AY QY MY ((9991451 / 10000000 : ℚ),(9991453 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
