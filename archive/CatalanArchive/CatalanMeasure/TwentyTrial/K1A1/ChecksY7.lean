module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY7 : integerGapOK AZY ((99517 / 625000 : ℚ),(796137 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY7 : shiftedColumnBracketOK C Vc V AY QY MY ((99517 / 625000 : ℚ),(796137 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
