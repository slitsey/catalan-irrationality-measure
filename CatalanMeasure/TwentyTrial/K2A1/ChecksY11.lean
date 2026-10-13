module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY11 : integerGapOK AZY ((105613 / 1000000 : ℚ),(1 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketY11 : shiftedColumnBracketOK C Vc V AY QY MY ((105613 / 1000000 : ℚ),(1 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
