module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY35 : integerGapOK AZY ((3612421 / 5000000 : ℚ),(3 / 4 : ℚ),false)=true :=by decide +kernel
theorem bracketY35 : shiftedColumnBracketOK C Vc V AY QY MY ((3612421 / 5000000 : ℚ),(3 / 4 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
