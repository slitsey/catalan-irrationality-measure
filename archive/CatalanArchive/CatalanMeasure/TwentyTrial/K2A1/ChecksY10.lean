module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY10 : integerGapOK AZY ((8251 / 78125 : ℚ),(105613 / 1000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY10 : shiftedColumnBracketOK C Vc V AY QY MY ((8251 / 78125 : ℚ),(105613 / 1000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
