module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY59 : integerGapOK AZY ((4907677 / 5000000 : ℚ),(1969 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketY59 : shiftedColumnBracketOK C Vc V AY QY MY ((4907677 / 5000000 : ℚ),(1969 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
