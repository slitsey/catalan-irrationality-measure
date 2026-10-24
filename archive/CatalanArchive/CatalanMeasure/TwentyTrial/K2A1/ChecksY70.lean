module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY70 : integerGapOK AZY ((193929 / 200000 : ℚ),(9696453 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY70 : shiftedColumnBracketOK C Vc V AY QY MY ((193929 / 200000 : ℚ),(9696453 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
