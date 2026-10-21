module
public import CatalanFrames.P6Hybrid.QuarterSelect
public import CatalanFrames.P6Hybrid.QuarterPeriodicContent
public import CatalanFrames.P6.Final
public import CatalanCore.Measure.Pinned
@[expose] public section
open CatalanCore CatalanCore.Rect CatalanFrames.P6
namespace CatalanFrames.P6Hybrid.Quarter

noncomputable abbrev family : PolyFamily := commonMinorFam p6Frame Adm 1

/-- Checked final assembly. The sole remaining input is the quarter analytic
certificate; this conditional interface is not an exported numerical bound. -/
theorem measure_of_decay
    (hD : HasDecay family (4639/1000) (161/20)) :
    family.MeasureLB (((153/10 : ℚ)) : ℝ) := by
  have hC : HasContent family (((15791/3840 : ℚ)) : ℝ) := by
    convert Periodic.hasContent 1 using 1 <;> norm_num
  have hD' : HasDecay family (((4639/1000 : ℚ)) : ℝ) (((161/20 : ℚ)) : ℝ) := by
    convert hD using 1 <;> norm_num
  exact Measure.measure_of_family_pin_leC family
    (c := 161/20) (Λ := 15791/3840) (D := 4639/1000)
    (α := 1) (β := 2) (s := 1) (E' := 153/10)
    hC hD' (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by convert hasNVPin using 1 <;> norm_num) (by convert p6_window_square using 1 <;> norm_num) (by norm_num)

theorem chi3_measure_of_decay
    (hD : HasDecay family (4639/1000) (161/20)) :
    Measure.MeasureLBAt chi3L2 (153/10) := by
  have h' : Measure.MeasureLBAt p6Frame.const (153/10) := by
    have hb := (Measure.MeasureLB_iff family (((153/10 : ℚ)) : ℝ)).mp (measure_of_decay hD)
    convert hb using 1 <;> norm_num [family, commonMinorFam]
  rw [chi3L2_eq]
  exact h'.affine (by norm_num) 4 0 (by norm_num)

end CatalanFrames.P6Hybrid.Quarter
#print axioms CatalanFrames.P6Hybrid.Quarter.chi3_measure_of_decay
