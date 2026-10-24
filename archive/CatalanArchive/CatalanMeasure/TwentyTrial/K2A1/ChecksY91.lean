module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY91 : integerGapOK AZY ((199951 / 200000 : ℚ),(199979 / 200000 : ℚ),false)=true :=by decide +kernel
theorem bracketY91 : shiftedColumnBracketOK C Vc V AY QY MY ((199951 / 200000 : ℚ),(199979 / 200000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
