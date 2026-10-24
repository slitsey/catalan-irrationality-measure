module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX10 : integerGapOK AZX ((-49951 / 50000 : ℚ),(-19961 / 20000 : ℚ),false)=true :=by decide +kernel
theorem bracketX10 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-49951 / 50000 : ℚ),(-19961 / 20000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
