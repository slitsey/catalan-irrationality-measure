module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY65 : integerGapOK AZY ((498167 / 500000 : ℚ),(4981671 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY65 : shiftedColumnBracketOK C Vc V AY QY MY ((498167 / 500000 : ℚ),(4981671 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
