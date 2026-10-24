module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY47 : integerGapOK AZY ((720617 / 1000000 : ℚ),(3 / 4 : ℚ),false)=true :=by decide +kernel
theorem bracketY47 : shiftedColumnBracketOK C Vc V AY QY MY ((720617 / 1000000 : ℚ),(3 / 4 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
