module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY23 : integerGapOK AZY ((396739 / 1250000 : ℚ),(3 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketY23 : shiftedColumnBracketOK C Vc V AY QY MY ((396739 / 1250000 : ℚ),(3 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
