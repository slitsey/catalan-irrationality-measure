module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketY_21 : shiftedColumnBracketOK C Vc V AY QY MY ((8381767 / 12500000 : ℚ),(67054139 / 100000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_23 : shiftedColumnBracketOK C Vc V AY QY MY ((1803783 / 2500000 : ℚ),(72151323 / 100000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_25 : shiftedColumnBracketOK C Vc V AY QY MY ((77189757 / 100000000 : ℚ),(120609 / 156250 : ℚ),true)=true := by decide +kernel
theorem bracketY_27 : shiftedColumnBracketOK C Vc V AY QY MY ((40758609 / 50000000 : ℚ),(81517221 / 100000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_29 : shiftedColumnBracketOK C Vc V AY QY MY ((8560241 / 10000000 : ℚ),(85602413 / 100000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.FirstStrongTrial
