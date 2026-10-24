module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX108 : integerGapOK AZX ((2674589 / 5000000 : ℚ),(281 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketX108 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((2674589 / 5000000 : ℚ),(281 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
