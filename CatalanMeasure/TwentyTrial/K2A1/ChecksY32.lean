module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY32 : integerGapOK AZY ((4963239 / 10000000 : ℚ),(1 / 2 : ℚ),false)=true :=by decide +kernel
theorem bracketY32 : shiftedColumnBracketOK C Vc V AY QY MY ((4963239 / 10000000 : ℚ),(1 / 2 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
