module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY43 : integerGapOK AZY ((2138901 / 2500000 : ℚ),(4277803 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY43 : shiftedColumnBracketOK C Vc V AY QY MY ((2138901 / 2500000 : ℚ),(4277803 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
