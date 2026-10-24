module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketY_1 : shiftedColumnBracketOK C Vc V AY QY MY ((3274023 / 100000000 : ℚ),(1637013 / 50000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_3 : shiftedColumnBracketOK C Vc V AY QY MY ((1927083 / 25000000 : ℚ),(1541667 / 20000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_5 : shiftedColumnBracketOK C Vc V AY QY MY ((15396267 / 100000000 : ℚ),(1539627 / 10000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_7 : shiftedColumnBracketOK C Vc V AY QY MY ((21519511 / 100000000 : ℚ),(10759757 / 50000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_9 : shiftedColumnBracketOK C Vc V AY QY MY ((1820423 / 6250000 : ℚ),(29126771 / 100000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.FirstStrongTrial
