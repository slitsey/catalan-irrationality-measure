module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY45 : integerGapOK AZY ((7 / 8 : ℚ),(555691 / 625000 : ℚ),false)=true :=by decide +kernel
theorem bracketY45 : shiftedColumnBracketOK C Vc V AY QY MY ((7 / 8 : ℚ),(555691 / 625000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
