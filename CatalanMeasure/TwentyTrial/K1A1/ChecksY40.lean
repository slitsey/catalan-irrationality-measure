module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY40 : integerGapOK AZY ((8151847 / 10000000 : ℚ),(163037 / 200000 : ℚ),true)=true :=by decide +kernel
theorem bracketY40 : shiftedColumnBracketOK C Vc V AY QY MY ((8151847 / 10000000 : ℚ),(163037 / 200000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
