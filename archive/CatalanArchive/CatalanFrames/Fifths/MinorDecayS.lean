module
public import CatalanFrames.Thirds.MinorDecayS
public import CatalanFrames.Fifths.Admissible
@[expose] public section
open CatalanCore CatalanCore.Rect
namespace CatalanFrames.Fifths
/-! Deferred shared-decay adapter. Reuses certS: rho1/4096,epsilon1/1000,alpha1/8,slope5/2.
No fresh numerical certificate and no chi3-quarter numeric constants enter here. -/
theorem fifths1_minorDecayS : HasDecay (commonMinorFam fifths1 FifthsAdm 1)
    ((390557/100000 : ℚ) : ℝ) ((18386549/2500000 : ℚ) : ℝ) := by
  exact Thirds.hasDecay_commonMinorFam_certS (fifths1_decayOKs' (5/2) (by norm_num))
    rfl (a := 9/8) (by norm_num) 1 (by simpa using adm_window)
theorem fifths2_minorDecayS : HasDecay (commonMinorFam fifths2 FifthsAdm 1)
    ((390557/100000 : ℚ) : ℝ) ((18386549/2500000 : ℚ) : ℝ) := by
  exact Thirds.hasDecay_commonMinorFam_certS (fifths2_decayOKs' (5/2) (by norm_num))
    rfl (a := 9/8) (by norm_num) 1 (by simpa using adm_window)
theorem fifths3_minorDecayS : HasDecay (commonMinorFam fifths3 FifthsAdm 1)
    ((390557/100000 : ℚ) : ℝ) ((18386549/2500000 : ℚ) : ℝ) := by
  exact Thirds.hasDecay_commonMinorFam_certS (fifths3_decayOKs' (5/2) (by norm_num))
    rfl (a := 9/8) (by norm_num) 1 (by simpa using adm_window)
theorem fifths4_minorDecayS : HasDecay (commonMinorFam fifths4 FifthsAdm 1)
    ((390557/100000 : ℚ) : ℝ) ((18386549/2500000 : ℚ) : ℝ) := by
  exact Thirds.hasDecay_commonMinorFam_certS (fifths4_decayOKs' (5/2) (by norm_num))
    rfl (a := 9/8) (by norm_num) 1 (by simpa using adm_window)
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.fifths1_minorDecayS
#print axioms CatalanFrames.Fifths.fifths2_minorDecayS
#print axioms CatalanFrames.Fifths.fifths3_minorDecayS
#print axioms CatalanFrames.Fifths.fifths4_minorDecayS
