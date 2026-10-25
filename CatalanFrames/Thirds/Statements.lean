module

public import CatalanFrames.Thirds.Assembly
public import CatalanFrames.Thirds.ContentInstances
public import CatalanFrames.Thirds.MinorDecayS
public import CatalanFrames.Thirds.TargetConstants

@[expose] public section

/-! # Final statements: `L(2,χ₋₃) ± π²/9` (= `L ± (2/3) ζ(2)`), exponent `1091/100`

Frames `thirdsAc` (`s = 1/3`, norm `9`) and `thirdsBc` (`s = 2/3`, norm `9`).
`thirdsAc.const = -(L + π²/9)/2`, `thirdsBc.const = (L - π²/9)/2`.
-/

open CatalanCore CatalanFrames.P6

namespace CatalanFrames.Thirds

/-- The exact numerical check behind the exponent. -/
theorem thirds_exponent_check :
    (18386549 / 2500000 : ℚ) / (390557 / 100000 - 32313 / 10000) ≤ 1091 / 100 := by
  norm_num

private theorem adm_exists : ∀ r : ℕ, 1 ≤ r → ∃ m, ThirdsAdm r m := fun r _ =>
  ⟨(r + 7) / 8, by unfold ThirdsAdm; omega⟩

private theorem adm_window (r m : ℕ) (h : ThirdsAdm r m) :
    (((1 / 8 : ℚ)) : ℝ) * r ≤ m ∧ (m : ℝ) ≤ (((1 / 8 : ℚ)) : ℝ) * r + 9 / 8 := by
  obtain ⟨h1, h2⟩ := h
  have a1 : (r : ℝ) ≤ 8 * m := by exact_mod_cast h1
  have a2 : (8 * m : ℝ) ≤ r + 9 := by exact_mod_cast h2
  push_cast
  constructor <;> linarith

private theorem measure_core (Fr : Frame)
    (hC : HasContent (CatalanCore.Rect.commonMinorFam Fr ThirdsAdm 1) (32313 / 10000))
    (hD : HasDecay (CatalanCore.Rect.commonMinorFam Fr ThirdsAdm 1)
      (((390557 / 100000 : ℚ)) : ℝ) (((18386549 / 2500000 : ℚ)) : ℝ))
    (hNV : HasNVPinC (CatalanCore.Rect.commonMinorFam Fr ThirdsAdm 1)
      (ClsIn 6 {1}) (PowBad 2) 1 2) :
    (CatalanCore.Rect.commonMinorFam Fr ThirdsAdm 1).MeasureLB (((1091 / 100 : ℚ)) : ℝ) :=
  thirds_measure_of_hyps _ (Λ := 32313 / 10000) (D := 390557 / 100000)
    (c := 18386549 / 2500000) (E' := 1091 / 100)
    (by convert hC using 1 <;> norm_num) hD (by norm_num) (by norm_num) (by norm_num) hNV
    thirds_exponent_check

/-- `L(2,χ₋₃) + (2/3) ζ(2)`: irrationality exponent `1091/100`. -/
theorem chi3_plus_zeta2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1091 / 100 : ℚ) : ℝ) + e)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          + Real.pi ^ 2 / 9) - (p : ℝ) / q| := by
  have hM := measure_core thirdsAc (thirdsAc_hasContent ThirdsAdm (fun _ _ h => h) 1)
    (thirdsAc_minorDecay (a := 9 / 8) (by norm_num) 1 adm_window)
    (thirdsAc_hasNVPinC ThirdsAdm adm_exists _ _ _ _)
  exact measureLBAt_of_const (T := chi3L2 + Real.pi ^ 2 / 9) (a := -1 / 2) (by norm_num)
    (by norm_num) thirdsAc_const hM

/-- `L(2,χ₋₃) - (2/3) ζ(2)`: irrationality exponent `1091/100`. -/
theorem chi3_minus_zeta2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1091 / 100 : ℚ) : ℝ) + e)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - Real.pi ^ 2 / 9) - (p : ℝ) / q| := by
  have hM := measure_core thirdsBc (thirdsBc_hasContent ThirdsAdm (fun _ _ h => h) 1)
    (thirdsBc_minorDecay (a := 9 / 8) (by norm_num) 1 adm_window)
    (thirdsBc_hasNVPinC ThirdsAdm adm_exists _ _ _ _)
  exact measureLBAt_of_const (T := chi3L2 - Real.pi ^ 2 / 9) (a := 1 / 2) (by norm_num)
    (by norm_num) thirdsBc_const hM

end CatalanFrames.Thirds

#print axioms CatalanFrames.Thirds.chi3_plus_zeta2_measure
#print axioms CatalanFrames.Thirds.chi3_minus_zeta2_measure
