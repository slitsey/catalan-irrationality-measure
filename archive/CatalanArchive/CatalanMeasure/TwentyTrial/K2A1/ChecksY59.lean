module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY59 : integerGapOK AZY ((1758399 / 2000000 : ℚ),(2227 / 2500 : ℚ),false)=true :=by decide +kernel
theorem bracketY59 : shiftedColumnBracketOK C Vc V AY QY MY ((1758399 / 2000000 : ℚ),(2227 / 2500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
