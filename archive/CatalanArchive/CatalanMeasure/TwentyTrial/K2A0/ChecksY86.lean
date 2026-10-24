module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY86 : integerGapOK AZY ((49951 / 50000 : ℚ),(9991443 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY86 : shiftedColumnBracketOK C Vc V AY QY MY ((49951 / 50000 : ℚ),(9991443 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
