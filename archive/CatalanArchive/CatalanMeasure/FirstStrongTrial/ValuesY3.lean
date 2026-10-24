module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketY_31 : shiftedColumnBracketOK C Vc V AY QY MY ((11130509 / 12500000 : ℚ),(3561763 / 4000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_33 : shiftedColumnBracketOK C Vc V AY QY MY ((11511451 / 12500000 : ℚ),(92091611 / 100000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_35 : shiftedColumnBracketOK C Vc V AY QY MY ((94569351 / 100000000 : ℚ),(47284677 / 50000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_37 : shiftedColumnBracketOK C Vc V AY QY MY ((96531579 / 100000000 : ℚ),(48265791 / 50000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_39 : shiftedColumnBracketOK C Vc V AY QY MY ((98035361 / 100000000 : ℚ),(24508841 / 25000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.FirstStrongTrial
