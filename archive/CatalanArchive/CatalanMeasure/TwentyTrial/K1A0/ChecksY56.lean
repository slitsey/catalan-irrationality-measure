module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY56 : integerGapOK AZY ((2412989 / 2500000 : ℚ),(969 / 1000 : ℚ),false)=true :=by decide +kernel
theorem bracketY56 : shiftedColumnBracketOK C Vc V AY QY MY ((2412989 / 2500000 : ℚ),(969 / 1000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
