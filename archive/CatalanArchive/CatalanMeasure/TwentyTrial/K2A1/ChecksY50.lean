module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY50 : integerGapOK AZY ((379391 / 500000 : ℚ),(781 / 1000 : ℚ),false)=true :=by decide +kernel
theorem bracketY50 : shiftedColumnBracketOK C Vc V AY QY MY ((379391 / 500000 : ℚ),(781 / 1000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
