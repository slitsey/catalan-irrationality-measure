module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY5 : integerGapOK AZY ((813999 / 10000000 : ℚ),(1 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketY5 : shiftedColumnBracketOK C Vc V AY QY MY ((813999 / 10000000 : ℚ),(1 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
