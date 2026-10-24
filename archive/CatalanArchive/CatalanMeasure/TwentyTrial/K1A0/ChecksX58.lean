module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX58 : integerGapOK AZX ((3315369 / 5000000 : ℚ),(331537 / 500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX58 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((3315369 / 5000000 : ℚ),(331537 / 500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
