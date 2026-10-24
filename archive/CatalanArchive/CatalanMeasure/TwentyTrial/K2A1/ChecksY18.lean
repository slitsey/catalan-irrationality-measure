module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY18 : integerGapOK AZY ((1 / 4 : ℚ),(2653169 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY18 : shiftedColumnBracketOK C Vc V AY QY MY ((1 / 4 : ℚ),(2653169 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
