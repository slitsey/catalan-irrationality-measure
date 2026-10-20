module

public import CatalanArchive.CatalanFrames.LambdaMirror.Final
public import CatalanArchive.CatalanFrames.LambdaMirror.NVStrong

/-!
# λ′ final statement with `κ = 0` nonvanishing: exponent `c/η` (mirror of `Lambda.FinalStrong`).
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.LambdaMirror

theorem mirDvdRule_hasWindow : mirDvdRule.HasWindow :=
  PrimeRule.ofDvd_hasWindow 4 1 isUnit_mod4_one

theorem hNVPin_q : HasNVPin (PolyFamily.ofFrame mirFrame) mirDvdRule (((3 / 2 : ℚ)) : ℝ)
    (((7 / 2 : ℚ)) : ℝ) := by
  have := hasNVPin_mir
  push_cast
  exact this

theorem mirFamily_measure_kappa0 :
    (PolyFamily.ofFrame mirFrame).MeasureLB
      (((68726 / 10000 / (31111 / 10000 - 313 / 105) : ℚ)) : ℝ) :=
  Measure.measure_of_family_pin_le _ hΛ_q hD_cert (by norm_num) (by norm_num) mirDvdRule
    (by norm_num) (by norm_num) (by rw [mirDvdRule_s]; norm_num) hNVPin_q mirDvdRule_hasWindow
    le_rfl

end CatalanFrames.LambdaMirror
