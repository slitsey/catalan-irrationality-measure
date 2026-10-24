module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY60 : integerGapOK AZY ((2227 / 2500 : ℚ),(1132311 / 1250000 : ℚ),false)=true :=by decide +kernel
theorem bracketY60 : shiftedColumnBracketOK C Vc V AY QY MY ((2227 / 2500 : ℚ),(1132311 / 1250000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
