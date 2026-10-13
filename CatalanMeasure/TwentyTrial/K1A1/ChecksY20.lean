module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY20 : integerGapOK AZY ((869503 / 2000000 : ℚ),(219 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketY20 : shiftedColumnBracketOK C Vc V AY QY MY ((869503 / 2000000 : ℚ),(219 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
