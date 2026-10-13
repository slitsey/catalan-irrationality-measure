module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY16 : integerGapOK AZY ((313 / 2000 : ℚ),(453711 / 2500000 : ℚ),false)=true :=by decide +kernel
theorem bracketY16 : shiftedColumnBracketOK C Vc V AY QY MY ((313 / 2000 : ℚ),(453711 / 2500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
