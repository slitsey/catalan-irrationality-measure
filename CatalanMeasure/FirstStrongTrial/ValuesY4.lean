module
public import CatalanMeasure.FirstStrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketY_41 : shiftedColumnBracketOK C Vc V AY QY MY ((49484471 / 50000000 : ℚ),(19793789 / 20000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_43 : shiftedColumnBracketOK C Vc V AY QY MY ((19921293 / 20000000 : ℚ),(24901617 / 25000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_45 : shiftedColumnBracketOK C Vc V AY QY MY ((99831853 / 100000000 : ℚ),(6239491 / 6250000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.FirstStrongTrial
