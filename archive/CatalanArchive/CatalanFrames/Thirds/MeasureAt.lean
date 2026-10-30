module

public import CatalanFrames.Thirds.ContentSharp
public import CatalanFrames.Thirds.Assembly
public import CatalanFrames.Thirds.TargetConstants

@[expose] public section

/-! # Both target measure bounds from a thirds decay hypothesis

The content price is the exact finite-table sum. The decay exponents and resulting
measure bound are parameters; this module imports no numerical decay certificate.
-/

open CatalanCore CatalanCore.Rect CatalanFrames.P6

namespace CatalanFrames.Thirds

private theorem sharp_adm_exists : ∀ r : ℕ, 1 ≤ r → ∃ m, ThirdsAdm r m := fun r _ =>
  ⟨(r + 7) / 8, by unfold ThirdsAdm; omega⟩

/-- Transfer any suitable common-minor decay bound to the plus target. -/
theorem chi3_plus_zeta2_measure_of_decay {D c E : ℚ}
    (hD : HasDecay (commonMinorFam thirdsAc ThirdsAdm 1) (D : ℝ) (c : ℝ))
    (hΛD : thirdsSharpPrice < D) (hc : 0 < c) (hs : D - thirdsSharpPrice < 1)
    (hE : c / (D - thirdsSharpPrice) ≤ E) :
    Measure.MeasureLBAt (chi3L2 + Real.pi ^ 2 / 9) (E : ℝ) := by
  have hM := thirds_measure_of_hyps (commonMinorFam thirdsAc ThirdsAdm 1)
    (Λ := thirdsSharpPrice) (D := D) (c := c) (E' := E)
    (thirdsAc_hasContent_sharp ThirdsAdm (fun _ _ h => h) 1) hD hΛD hc hs
    (thirdsAc_hasNVPinC ThirdsAdm sharp_adm_exists _ _ _ _) hE
  have hE0 : 0 ≤ E := le_trans (le_of_lt (div_pos hc (sub_pos.mpr hΛD))) hE
  exact measureLBAt_of_const (T := chi3L2 + Real.pi ^ 2 / 9) (a := -1 / 2)
    (by norm_num) hE0 thirdsAc_const hM

/-- Transfer any suitable common-minor decay bound to the minus target. -/
theorem chi3_minus_zeta2_measure_of_decay {D c E : ℚ}
    (hD : HasDecay (commonMinorFam thirdsBc ThirdsAdm 1) (D : ℝ) (c : ℝ))
    (hΛD : thirdsSharpPrice < D) (hc : 0 < c) (hs : D - thirdsSharpPrice < 1)
    (hE : c / (D - thirdsSharpPrice) ≤ E) :
    Measure.MeasureLBAt (chi3L2 - Real.pi ^ 2 / 9) (E : ℝ) := by
  have hM := thirds_measure_of_hyps (commonMinorFam thirdsBc ThirdsAdm 1)
    (Λ := thirdsSharpPrice) (D := D) (c := c) (E' := E)
    (thirdsBc_hasContent_sharp ThirdsAdm (fun _ _ h => h) 1) hD hΛD hc hs
    (thirdsBc_hasNVPinC ThirdsAdm sharp_adm_exists _ _ _ _) hE
  have hE0 : 0 ≤ E := le_trans (le_of_lt (div_pos hc (sub_pos.mpr hΛD))) hE
  exact measureLBAt_of_const (T := chi3L2 - Real.pi ^ 2 / 9) (a := 1 / 2)
    (by norm_num) hE0 thirdsBc_const hM

end CatalanFrames.Thirds

#print axioms CatalanFrames.Thirds.chi3_plus_zeta2_measure_of_decay
#print axioms CatalanFrames.Thirds.chi3_minus_zeta2_measure_of_decay
