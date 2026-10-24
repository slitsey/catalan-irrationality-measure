module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX122 : integerGapOK AZX ((3895861 / 5000000 : ℚ),(1947931 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX122 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((3895861 / 5000000 : ℚ),(1947931 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
