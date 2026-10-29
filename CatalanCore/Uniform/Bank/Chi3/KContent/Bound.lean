import CatalanCore.Uniform.Bank.Chi3.KContent.Link
import CatalanCore.Uniform.Bank.Chi3New.Final
set_option Elab.async false

/-! # The irrationality measure of `L(2, χ₋₃)` on the k-shift route with the prefix layer

`chi3_measureLB_of_decay` (content `Λ = kData.Λ = 4.0959277673…`, all even scales, no rank layer)
with the decay `chi3_decay` (`D = Dt`, `c = ccert`):
`μ(L(2, χ₋₃)) ≤ ccert / (Dt - Λ) = 13.70451624… ≤ 13.7046`. -/

namespace CatalanCore.Uniform.Bank.Chi3.KContent
open CatalanCore CatalanCore.Uniform CatalanFrames.P6 CatalanCore.Uniform.Bank.Chi3New
  CatalanCore.Uniform.Bank.Chi3 CatalanCore.Uniform.Decay.Cert

theorem kData_Λ_eq : kData.Λ =
    225706514569840812587646472267088130901573531845819693981955101571429004212021774333976142337325032023820324915415861 /
      55105101308379468249764243581140517776104156182333546862848918712563705179921864016722641907400253805397160894208000 := by
  decide +kernel

/-- **Measure of the even-scale block family with the prefix-layer content.** -/
theorem chi3_measureLB_k :
    ((G12.family p6Frame kDepth0).restrictAdm (fun i => i.1 % 2 = 0)).MeasureLB
      ((1 : ℝ) * ((37521870783566737 / 5000000000000000 : ℚ) : ℝ) /
        (((4643511791526209475773 / 1000000000000000000000 : ℚ) : ℝ) - ((kData.Λ : ℚ) : ℝ))) := by
  have hD0 := chi3_decay kDepth0
  rw [Dchi_Dt, Dchi_ccert] at hD0
  have hη : (kData.Λ : ℚ) < 4643511791526209475773 / 1000000000000000000000 := by
    rw [kData_Λ_eq]; norm_num
  exact chi3_measureLB_of_decay hD0 (by exact_mod_cast hη) (by norm_num)

theorem chi3_X_le_k : (1 : ℝ) * ((37521870783566737 / 5000000000000000 : ℚ) : ℝ) /
    (((4643511791526209475773 / 1000000000000000000000 : ℚ) : ℝ) - ((kData.Λ : ℚ) : ℝ)) ≤
      ((137046 / 10000 : ℚ) : ℝ) := by
  rw [kData_Λ_eq]
  push_cast
  rw [div_le_iff₀ (by norm_num)]
  norm_num

/-- **`μ(L(2, χ₋₃)) ≤ 13.7046`** (certified exponent `ccert / (Dt - Λ) = 13.70451624…`). -/
theorem chi3_measure_L2_k : Measure.MeasureLBAt chi3L2 ((137046 / 10000 : ℚ) : ℝ) := by
  have h0 := (Measure.MeasureLB_iff _ _).mp chi3_measureLB_k
  have h' : Measure.MeasureLBAt p6Frame.const ((137046 / 10000 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono chi3_X_le_k h0
  have he : chi3L2 = ((4 : ℚ) : ℝ) * p6Frame.const + ((0 : ℚ) : ℝ) := by
    rw [p6Frame_const]; push_cast; ring
  rw [he]
  exact h'.affine (by norm_num) 4 0 (by norm_num)

end CatalanCore.Uniform.Bank.Chi3.KContent

#print axioms CatalanCore.Uniform.Bank.Chi3.KContent.chi3_measureLB_k
#print axioms CatalanCore.Uniform.Bank.Chi3.KContent.chi3_measure_L2_k
