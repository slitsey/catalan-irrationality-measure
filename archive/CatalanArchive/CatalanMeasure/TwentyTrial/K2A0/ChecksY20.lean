module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY20 : integerGapOK AZY ((481913 / 2000000 : ℚ),(2409567 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY20 : shiftedColumnBracketOK C Vc V AY QY MY ((481913 / 2000000 : ℚ),(2409567 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
