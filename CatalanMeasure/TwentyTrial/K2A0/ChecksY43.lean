module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY43 : integerGapOK AZY ((86 / 125 : ℚ),(431 / 625 : ℚ),false)=true :=by decide +kernel
theorem bracketY43 : shiftedColumnBracketOK C Vc V AY QY MY ((86 / 125 : ℚ),(431 / 625 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
