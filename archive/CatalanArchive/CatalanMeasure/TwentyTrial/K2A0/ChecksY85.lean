module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY85 : integerGapOK AZY ((1996293 / 2000000 : ℚ),(49951 / 50000 : ℚ),false)=true :=by decide +kernel
theorem bracketY85 : shiftedColumnBracketOK C Vc V AY QY MY ((1996293 / 2000000 : ℚ),(49951 / 50000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
