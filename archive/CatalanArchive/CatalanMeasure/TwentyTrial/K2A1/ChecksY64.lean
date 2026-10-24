module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY64 : integerGapOK AZY ((373019 / 400000 : ℚ),(9325477 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY64 : shiftedColumnBracketOK C Vc V AY QY MY ((373019 / 400000 : ℚ),(9325477 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
