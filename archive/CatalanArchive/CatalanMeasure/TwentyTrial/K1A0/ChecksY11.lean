module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY11 : integerGapOK AZY ((131999 / 625000 : ℚ),(1 / 4 : ℚ),false)=true :=by decide +kernel
theorem bracketY11 : shiftedColumnBracketOK C Vc V AY QY MY ((131999 / 625000 : ℚ),(1 / 4 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
