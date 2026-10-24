module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY87 : integerGapOK AZY ((9991453 / 10000000 : ℚ),(99951 / 100000 : ℚ),false)=true :=by decide +kernel
theorem bracketY87 : shiftedColumnBracketOK C Vc V AY QY MY ((9991453 / 10000000 : ℚ),(99951 / 100000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
