module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY22 : integerGapOK AZY ((317391 / 1000000 : ℚ),(396739 / 1250000 : ℚ),true)=true :=by decide +kernel
theorem bracketY22 : shiftedColumnBracketOK C Vc V AY QY MY ((317391 / 1000000 : ℚ),(396739 / 1250000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
