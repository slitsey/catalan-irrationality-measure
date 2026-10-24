module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY4 : integerGapOK AZY ((720563 / 10000000 : ℚ),(144113 / 2000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY4 : shiftedColumnBracketOK C Vc V AY QY MY ((720563 / 10000000 : ℚ),(144113 / 2000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
