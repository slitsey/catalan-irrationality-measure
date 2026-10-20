module

public import CatalanFrames.P6Hybrid.MinorContent
public import CatalanFrames.P6Hybrid.MinorDecay
public import CatalanFrames.P6Hybrid.MinorSelect
public import CatalanFrames.P6Hybrid.WindowSquare
public import CatalanFrames.P6Hybrid.MinorFinal
public import CatalanFrames.P6.Final

@[expose] public section

open CatalanCore CatalanCore.Rect CatalanFrames.P6

namespace CatalanFrames.P6Hybrid

/-- The budget-three common-deletion family, with the original degree budget. -/
noncomputable abbrev p6MinorFam : PolyFamily := commonMinorFam p6Frame P6Adm9 3

/-- The checked analytic, content, window and numerical assembly; the concrete
finite-field nonvanishing theorem is supplied separately. -/
theorem p6_minor_measure_of_pin
    (hNV : HasNVPinC p6MinorFam P6Cls1 P6BadSquare (51 / 20) (59 / 20)) :
    p6MinorFam.MeasureLB (((37 / 2 : ℚ)) : ℝ) := by
  have hΛ : HasContent p6MinorFam (((10339 / 3072 : ℚ)) : ℝ) := by
    convert p6_minor_content 3 using 1 <;> norm_num
  have hD : HasDecay p6MinorFam (((37251 / 10000 : ℚ)) : ℝ) (((66510 / 10000 : ℚ)) : ℝ) := by
    convert p6_minor_decay 3 using 1 <;> norm_num
  have hNV' : HasNVPinC p6MinorFam P6Cls1 P6BadSquare
      (((51 / 20 : ℚ)) : ℝ) (((59 / 20 : ℚ)) : ℝ) := by
    convert hNV using 1 <;> norm_num
  exact Measure.measure_of_family_pin_leC p6MinorFam
    (c := 66510 / 10000) (Λ := 10339 / 3072) (D := 37251 / 10000)
    (α := 51 / 20) (β := 59 / 20) (s := 1) (E' := 37 / 2)
    hΛ hD (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hNV' p6_window_square (by norm_num)

/-- The bounded-deletion family gives the unconditional bound `18.50`. -/
theorem p6_minor_measure : p6MinorFam.MeasureLB (((37 / 2 : ℚ)) : ℝ) :=
  p6_minor_measure_of_pin p6_minor_hasNVPin

/-- `μ(L(2, χ₋₃)) ≤ 18.50`. -/
theorem chi3_hybrid_measure_minor :
    Measure.MeasureLBAt chi3L2 (((37 / 2 : ℚ)) : ℝ) := by
  have h' : Measure.MeasureLBAt p6Frame.const (((37 / 2 : ℚ)) : ℝ) := p6_minor_measure
  rw [chi3L2_eq]
  exact h'.affine (by norm_num) 4 0 (by norm_num)

#print axioms chi3_hybrid_measure_minor

end CatalanFrames.P6Hybrid
