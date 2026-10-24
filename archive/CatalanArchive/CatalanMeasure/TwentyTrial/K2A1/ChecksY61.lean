module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY61 : integerGapOK AZY ((1132311 / 1250000 : ℚ),(9058491 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY61 : shiftedColumnBracketOK C Vc V AY QY MY ((1132311 / 1250000 : ℚ),(9058491 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
