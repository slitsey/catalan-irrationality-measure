module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY76 : integerGapOK AZY ((9902421 / 10000000 : ℚ),(9902423 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY76 : shiftedColumnBracketOK C Vc V AY QY MY ((9902421 / 10000000 : ℚ),(9902423 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
