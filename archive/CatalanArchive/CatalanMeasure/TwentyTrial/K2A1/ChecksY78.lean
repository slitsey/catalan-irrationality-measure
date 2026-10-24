module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY78 : integerGapOK AZY ((4961 / 5000 : ℚ),(397933 / 400000 : ℚ),false)=true :=by decide +kernel
theorem bracketY78 : shiftedColumnBracketOK C Vc V AY QY MY ((4961 / 5000 : ℚ),(397933 / 400000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
