module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY92 : integerGapOK AZY ((199979 / 200000 : ℚ),(9998953 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY92 : shiftedColumnBracketOK C Vc V AY QY MY ((199979 / 200000 : ℚ),(9998953 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
