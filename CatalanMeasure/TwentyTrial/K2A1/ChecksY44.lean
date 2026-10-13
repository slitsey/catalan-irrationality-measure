module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY44 : integerGapOK AZY ((6920071 / 10000000 : ℚ),(719 / 1000 : ℚ),false)=true :=by decide +kernel
theorem bracketY44 : shiftedColumnBracketOK C Vc V AY QY MY ((6920071 / 10000000 : ℚ),(719 / 1000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
