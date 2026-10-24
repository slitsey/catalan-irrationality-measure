module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY20 : integerGapOK AZY ((66327 / 156250 : ℚ),(219 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketY20 : shiftedColumnBracketOK C Vc V AY QY MY ((66327 / 156250 : ℚ),(219 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
