module

public import CatalanFrames.P6Hybrid.ValOneRegular
public import CatalanFrames.P6Hybrid.WindowSquare

@[expose] public section

/-!
# The square-divisor prime rule for the P6 hybrid

The shared valuation-one argument changes only nonvanishing and prime
selection. The existing family, content and decay certificates are reused.
-/

open Filter CatalanCore CatalanCore.Rect CatalanFrames.P6

namespace CatalanFrames.P6Hybrid

theorem p6_hasNVC_square :
    HasNVC p6FamW P6Cls1 P6BadSquare (((2 / 5 : ℚ)) : ℝ) (((2 / 5 : ℚ)) : ℝ) := by
  refine p6_hasNVC_of_regular p6_pairNV_square
    (fun ℓ _ _ p q _ _ hbad => not_pow_dvd_rat_den ℓ 2 p q hbad) ?_
  intro ℓ hℓ hl0 hc
  obtain ⟨t, r, m, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    pinned_pair_exists_wide ℓ hc.mod6 hl0
  exact ⟨t, r, m, h1, h2, ⟨h3, h4⟩, h5, h6, h7, h8⟩

/-- The current certificates with the square-divisor prime window give 21.16. -/
theorem p6_pair_measure_square : p6FamW.MeasureLB (((2116 / 100 : ℚ)) : ℝ) := by
  have hΛ : HasContent p6FamW (((10339 / 3072 : ℚ)) : ℝ) := by
    have e : (((10339 / 3072 : ℚ)) : ℝ) = 10339 / 3072 := by push_cast; norm_num
    rw [e]; exact p6_pair_content_of (fun _ _ h => h)
  exact Measure.measure_of_family_leC p6FamW (c := 66510 / 10000) (Λ := 10339 / 3072)
    (D := 37251 / 10000) (g₁ := 2 / 5) (g₂ := 2 / 5) (s := 1) (E' := 2116 / 100)
    hΛ (p6_pair_decay_of (fun _ _ h => h)) (by norm_num) (by norm_num) (by norm_num)
    ⟨by norm_num, le_rfl⟩ p6_hasNVC_square p6_window_square (by norm_num [measureExp])

/-- `μ(L(2, χ₋₃)) ≤ 21.16`. -/
theorem chi3_hybrid_measure_square :
    Measure.MeasureLBAt chi3L2 (((2116 / 100 : ℚ)) : ℝ) := by
  have h' : Measure.MeasureLBAt p6Frame.const (((2116 / 100 : ℚ)) : ℝ) :=
    p6_pair_measure_square
  rw [chi3L2_eq]
  exact h'.affine (by norm_num) 4 0 (by norm_num)

#print axioms chi3_hybrid_measure_square

end CatalanFrames.P6Hybrid
