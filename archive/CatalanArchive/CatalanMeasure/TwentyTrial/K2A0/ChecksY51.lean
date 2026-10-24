module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY51 : integerGapOK AZY ((7800869 / 10000000 : ℚ),(203 / 250 : ℚ),false)=true :=by decide +kernel
theorem bracketY51 : shiftedColumnBracketOK C Vc V AY QY MY ((7800869 / 10000000 : ℚ),(203 / 250 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
