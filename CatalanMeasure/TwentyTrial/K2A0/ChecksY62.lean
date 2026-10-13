module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY62 : integerGapOK AZY ((571941 / 625000 : ℚ),(9151059 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY62 : shiftedColumnBracketOK C Vc V AY QY MY ((571941 / 625000 : ℚ),(9151059 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
