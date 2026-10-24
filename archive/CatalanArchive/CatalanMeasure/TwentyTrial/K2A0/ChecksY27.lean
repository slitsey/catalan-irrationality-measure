module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY27 : integerGapOK AZY ((3547123 / 10000000 : ℚ),(3 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketY27 : shiftedColumnBracketOK C Vc V AY QY MY ((3547123 / 10000000 : ℚ),(3 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
