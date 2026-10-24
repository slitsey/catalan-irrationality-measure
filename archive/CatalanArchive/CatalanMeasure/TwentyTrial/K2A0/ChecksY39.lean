module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY39 : integerGapOK AZY ((2936609 / 5000000 : ℚ),(5 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketY39 : shiftedColumnBracketOK C Vc V AY QY MY ((2936609 / 5000000 : ℚ),(5 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
