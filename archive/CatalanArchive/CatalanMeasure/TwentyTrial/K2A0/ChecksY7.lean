module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY7 : integerGapOK AZY ((31 / 1000 : ℚ),(591589 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY7 : shiftedColumnBracketOK C Vc V AY QY MY ((31 / 1000 : ℚ),(591589 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
