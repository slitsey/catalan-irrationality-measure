module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY89 : integerGapOK AZY ((9997491 / 10000000 : ℚ),(9997493 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY89 : shiftedColumnBracketOK C Vc V AY QY MY ((9997491 / 10000000 : ℚ),(9997493 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
