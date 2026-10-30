import CatalanCore.Uniform.Decay.PairEnergy.Oracle
import CatalanCore.Uniform.Decay.Cert.PilotSevenths
set_option Elab.async false
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 20

/-!
# Pilot (lane D, package D6c): real pairs of the sevenths trial through the kernel

`pairOk sevData i j E = true` by `decide +kernel` for pairs of the 27-piece trial
(collinear self pair, collinear neighbours, transversal pairs sharing an endpoint, conjugate
pairs, general transversal pairs, far pairs).  `E` is a rounded-up value of the evaluator's
directed upper bound; independently, numerical midpoint quadrature agrees to 4 digits.
-/

namespace CatalanCore.Uniform.Decay.PairEnergy.Pilot

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Cert.Pilot

theorem p_0_0 : pairOk sevData 0 0 (1 / 500000) = true := by decide +kernel
theorem p_0_1 : pairOk sevData 0 1 (1 / 100000) = true := by decide +kernel
theorem p_0_5 : pairOk sevData 0 5 (1 / 9000) = true := by decide +kernel
theorem p_5_6 : pairOk sevData 5 6 (1 / 50) = true := by decide +kernel
theorem p_5_5 : pairOk sevData 5 5 (1 / 38) = true := by decide +kernel
theorem p_5_7 : pairOk sevData 5 7 (1 / 60) = true := by decide +kernel
theorem p_7_8 : pairOk sevData 7 8 (1 / 110) = true := by decide +kernel
theorem p_0_21 : pairOk sevData 0 21 (1 / 100000) = true := by decide +kernel
theorem p_21_21 : pairOk sevData 21 21 (1 / 100000) = true := by decide +kernel
theorem p_5_21 : pairOk sevData 5 21 (1 / 100000) = true := by decide +kernel
theorem p_7_22 : pairOk sevData 7 22 (1 / 100000) = true := by decide +kernel
theorem p_19_20 : pairOk sevData 19 20 (1 / 100000) = true := by decide +kernel

/-- The cap segment `[-r0, 0]` with density one, as an extra segment (cap-sigma blocks). -/
def capSeg : Seg :=
  { ax := -273 / 2000, ay := 0, bx := 0, byy := 0, coef := [1], M := 1, Lq := 273 / 2000, tau := 0 }

theorem c_0 : pairCheck (sevSegs.getD 0 capSeg) capSeg (1 / 990) = true := by decide +kernel
theorem c_4 : pairCheck (sevSegs.getD 4 capSeg) capSeg (7 / 10) = true := by decide +kernel
theorem c_5 : pairCheck (sevSegs.getD 5 capSeg) capSeg (1 / 5) = true := by decide +kernel
theorem c_7 : pairCheck (sevSegs.getD 7 capSeg) capSeg (1 / 7) = true := by decide +kernel
theorem c_9 : pairCheck (sevSegs.getD 9 capSeg) capSeg (1 / 9) = true := by decide +kernel
theorem c_12 : pairCheck (sevSegs.getD 12 capSeg) capSeg (1 / 7) = true := by decide +kernel
theorem c_20 : pairCheck (sevSegs.getD 20 capSeg) capSeg (1 / 100000) = true := by decide +kernel

/-- A pair energy bound as a statement about the real pair energy, through the oracle. -/
theorem pairE_5_6_le : Cells.pairE sevData ⟨5, by decide⟩ ⟨6, by decide⟩ ≤ ((1 / 50 : ℚ) : ℝ) :=
  pairOracle.pair_sound sevData (by decide +kernel) _ _ _ p_5_6

end CatalanCore.Uniform.Decay.PairEnergy.Pilot
