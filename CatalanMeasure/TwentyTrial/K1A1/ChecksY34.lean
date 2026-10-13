module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY34 : integerGapOK AZY ((7224839 / 10000000 : ℚ),(3612421 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY34 : shiftedColumnBracketOK C Vc V AY QY MY ((7224839 / 10000000 : ℚ),(3612421 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
