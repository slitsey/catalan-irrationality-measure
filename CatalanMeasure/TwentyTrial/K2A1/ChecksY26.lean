module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY26 : integerGapOK AZY ((1904043 / 5000000 : ℚ),(813 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketY26 : shiftedColumnBracketOK C Vc V AY QY MY ((1904043 / 5000000 : ℚ),(813 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
