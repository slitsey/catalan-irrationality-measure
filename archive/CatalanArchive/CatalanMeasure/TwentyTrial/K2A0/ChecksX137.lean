module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX137 : integerGapOK AZX ((1873633 / 2000000 : ℚ),(1171021 / 1250000 : ℚ),true)=true :=by decide +kernel
theorem bracketX137 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1873633 / 2000000 : ℚ),(1171021 / 1250000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
