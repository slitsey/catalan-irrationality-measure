module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY28 : integerGapOK AZY ((1228099 / 2000000 : ℚ),(6140497 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY28 : shiftedColumnBracketOK C Vc V AY QY MY ((1228099 / 2000000 : ℚ),(6140497 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
