module

public import CatalanFrames.Lambda.Final
public import CatalanFrames.Lambda.NVStrong

/-!
# λ final statement with `κ = 0` nonvanishing: exponent `c/η`

`measure_of_family_pin_le` with `HasNVPin lamFamily lamDvdRule (3/2) (7/2)`:
`c/η = 68726/10000 / (31111/10000 - 313/105) ≈ 52.81`, stated with a rational upper bound.
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.Lambda

theorem lamDvdRule_hasWindow : lamDvdRule.HasWindow := PrimeRule.ofDvd_hasWindow 4 3 isUnit_mod4_three

theorem hNVPin_q : HasNVPin (PolyFamily.ofFrame lamFrame) lamDvdRule (((3 / 2 : ℚ)) : ℝ)
    (((7 / 2 : ℚ)) : ℝ) := by
  have := hasNVPin_lam
  push_cast
  exact this

/-- Exponent `c/η` (exact value `(68726/10000)/(31111/10000 - 313/105)`). -/
theorem lamFamily_measure_kappa0 :
    (PolyFamily.ofFrame lamFrame).MeasureLB
      (((68726 / 10000 / (31111 / 10000 - 313 / 105) : ℚ)) : ℝ) :=
  Measure.measure_of_family_pin_le _ hΛ_q hD_cert (by norm_num) (by norm_num) lamDvdRule
    (by norm_num) (by norm_num) (by rw [lamDvdRule_s]; norm_num) hNVPin_q lamDvdRule_hasWindow
    le_rfl

end CatalanFrames.Lambda
