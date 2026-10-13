module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY39 : integerGapOK AZY ((5 / 8 : ℚ),(323037 / 500000 : ℚ),false)=true :=by decide +kernel
theorem bracketY39 : shiftedColumnBracketOK C Vc V AY QY MY ((5 / 8 : ℚ),(323037 / 500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
