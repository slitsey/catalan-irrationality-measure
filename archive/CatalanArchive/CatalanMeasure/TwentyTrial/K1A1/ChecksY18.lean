module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY18 : integerGapOK AZY ((3 / 8 : ℚ),(4347513 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY18 : shiftedColumnBracketOK C Vc V AY QY MY ((3 / 8 : ℚ),(4347513 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
