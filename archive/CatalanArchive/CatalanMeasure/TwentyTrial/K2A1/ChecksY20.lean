module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY20 : integerGapOK AZY ((2653171 / 10000000 : ℚ),(39 / 125 : ℚ),false)=true :=by decide +kernel
theorem bracketY20 : shiftedColumnBracketOK C Vc V AY QY MY ((2653171 / 10000000 : ℚ),(39 / 125 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
