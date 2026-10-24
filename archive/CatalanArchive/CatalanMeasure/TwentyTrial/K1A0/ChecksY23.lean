module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY23 : integerGapOK AZY ((2427313 / 5000000 : ℚ),(1 / 2 : ℚ),false)=true :=by decide +kernel
theorem bracketY23 : shiftedColumnBracketOK C Vc V AY QY MY ((2427313 / 5000000 : ℚ),(1 / 2 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
