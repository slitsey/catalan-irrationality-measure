module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY13 : integerGapOK AZY ((371961 / 1250000 : ℚ),(297569 / 1000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY13 : shiftedColumnBracketOK C Vc V AY QY MY ((371961 / 1250000 : ℚ),(297569 / 1000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
