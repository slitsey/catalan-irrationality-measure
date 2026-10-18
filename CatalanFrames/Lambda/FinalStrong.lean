module

public import CatalanFrames.Lambda.Final
public import CatalanFrames.Lambda.NVStrong

/-!
# λ final statements with strong nonvanishing (exponent `≈ 57.96 < 58`)

`HasNV lamFrame lamRule (3/4) (3/4)` (Theorem A shortcut) in place of the weak `(3/4, 1)`.
New theorem names; the existing 78 statements are untouched.
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.Lambda

theorem hg_strong : (0 : ℚ) < 3 / 4 ∧ (3 / 4 : ℚ) ≤ 3 / 4 := by norm_num

theorem hNV_strong_q :
    HasNV (PolyFamily.ofFrame lamFrame) lamRule (((3 / 4 : ℚ)) : ℝ) (((3 / 4 : ℚ)) : ℝ) := by
  have := hasNV_strong
  push_cast
  exact this

/-- The exponent `31682445459/546620000 ≈ 57.96`. -/
theorem lamFamily_measure_strong :
    (PolyFamily.ofFrame lamFrame).MeasureLB (((31682445459 / 546620000 : ℚ)) : ℝ) :=
  Measure.measure_of_frame_le lamFrame hΛ_q hD_cert (by norm_num) (by norm_num) lamRule
    lamRule_s_pos hg_strong hNV_strong_q lamRule_hasWindow
    (by rw [lamRule_s]; norm_num [measureExp])

theorem lambda_irrationalityMeasure_58_solution :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(58 : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
          - 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  obtain ⟨q₀, H⟩ := lamFamily_measure_strong (1 / 100) (by norm_num)
  refine ⟨max q₀ 1, fun p q hc hq => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_right _ _) hq
  have h := H p q (le_trans (le_max_left _ _) hq) (coprime_conv p q hc)
  rw [show (PolyFamily.ofFrame lamFrame).const = _ from const_eq] at h
  refine lt_of_le_of_lt ?_ h
  exact Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)

end CatalanFrames.Lambda
