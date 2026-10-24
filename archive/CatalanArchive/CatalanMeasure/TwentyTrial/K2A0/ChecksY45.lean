module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY45 : integerGapOK AZY ((3448001 / 5000000 : ℚ),(719 / 1000 : ℚ),false)=true :=by decide +kernel
theorem bracketY45 : shiftedColumnBracketOK C Vc V AY QY MY ((3448001 / 5000000 : ℚ),(719 / 1000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
