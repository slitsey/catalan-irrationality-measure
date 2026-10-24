module

public import CatalanFrames.Thirds.Window
public import CatalanCore.Measure.Pinned
public import CatalanCore.Measure.Scaling

@[expose] public section

/-! # Generic assembly for the thirds shifts (M10)

Content, decay and pinned nonvanishing enter as hypotheses; the prime window is
class `1 mod 6` with bad primes `l ^ 2 ∣ q`, `(α, β, s) = (1, 2, 1)`.
The exponent `E'` is a parameter.
-/

open CatalanCore

namespace CatalanFrames.Thirds

/-- Measure bound for any family with content `Λ`, decay `(D, c)` and pinned NV on
class `1 mod 6`, `D - Λ < 1`. -/
theorem thirds_measure_of_hyps (Fam : PolyFamily) {Λ D c E' : ℚ}
    (hC : HasContent Fam (Λ : ℝ)) (hD : HasDecay Fam (D : ℝ) (c : ℝ))
    (hΛD : Λ < D) (hc : 0 < c) (hs : D - Λ < 1)
    (hNV : HasNVPinC Fam (ClsIn 6 {1}) (PowBad 2) 1 2)
    (hE : c / (D - Λ) ≤ E') : Fam.MeasureLB (E' : ℝ) := by
  have hNV' : HasNVPinC Fam (ClsIn 6 {1}) (PowBad 2) ((1 : ℚ) : ℝ) ((2 : ℚ) : ℝ) := by
    simpa using hNV
  have hw : HasWindowC (ClsIn 6 {1}) (PowBad 2) (((1 : ℚ)) : ℝ) := by
    simpa using window_one_mod_six
  exact Measure.measure_of_family_pin_leC Fam (α := 1) (β := 2) (s := 1) hC hD hΛD hc
    (by norm_num) (by norm_num) (by linarith) hNV' hw hE

/-- Rescaling: if the family constant is a nonzero rational multiple of the target `T`,
the measure bound transfers to `T`. -/
theorem measureLBAt_of_const {Fam : PolyFamily} {E : ℚ} {T : ℝ} {a : ℚ} (ha : a ≠ 0)
    (hE : 0 ≤ E) (hconst : Fam.const = (a : ℝ) * T)
    (hM : Fam.MeasureLB (E : ℝ)) : Measure.MeasureLBAt T (E : ℝ) := by
  have h := (Measure.MeasureLB_iff Fam (E : ℝ)).mp hM
  have h2 := Measure.MeasureLBAt.affine (by exact_mod_cast hE) h a⁻¹ 0 (inv_ne_zero ha)
  rw [hconst] at h2
  have : ((a⁻¹ : ℚ) : ℝ) * ((a : ℝ) * T) + ((0 : ℚ) : ℝ) = T := by
    push_cast; field_simp; simp
  rwa [this] at h2

end CatalanFrames.Thirds

#print axioms CatalanFrames.Thirds.window_one_mod_six
#print axioms CatalanFrames.Thirds.thirds_measure_of_hyps
#print axioms CatalanFrames.Thirds.measureLBAt_of_const
