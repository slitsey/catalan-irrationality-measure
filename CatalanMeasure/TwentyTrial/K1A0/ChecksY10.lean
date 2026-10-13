module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY10 : integerGapOK AZY ((1055991 / 5000000 : ℚ),(131999 / 625000 : ℚ),true)=true :=by decide +kernel
theorem bracketY10 : shiftedColumnBracketOK C Vc V AY QY MY ((1055991 / 5000000 : ℚ),(131999 / 625000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
