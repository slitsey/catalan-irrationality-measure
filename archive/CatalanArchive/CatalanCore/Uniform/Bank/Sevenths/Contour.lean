import CatalanCore.Uniform.Bank.Sevenths.Frame
set_option Elab.async false

namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore

/-- The exact per-member pole gaps from trial A's source-hypotheses receipt. -/
theorem sevenths_contourGap (a : Fin 6) : (seventhsFrameAt a).ContourGap := by
  constructor
  · fin_cases a <;> norm_num [seventhsFrameAt, seventhNumerator, seventhsFrame]
  · intro i n
    change (if a.val < 3 then (1 - (seventhNumerator a : ℚ) / 7) / 2
        else ((seventhNumerator a : ℚ) / 7) / 2) ≤
      |(n : ℚ) + (![(seventhNumerator a : ℚ) / 7, 1] i) -
        (if a.val < 3 then (1 + (seventhNumerator a : ℚ) / 7) / 2
          else ((seventhNumerator a : ℚ) / 7) / 2)|
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · have hnq : (n : ℚ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      fin_cases a <;> fin_cases i <;>
        norm_num [seventhsFrameAt, seventhNumerator, seventhsFrame] <;>
        rw [abs_of_nonpos] <;> linarith
    · fin_cases a <;> fin_cases i <;>
        norm_num [seventhsFrameAt, seventhNumerator, seventhsFrame]
    · have hnq : (1 : ℚ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
      fin_cases a <;> fin_cases i <;>
        norm_num [seventhsFrameAt, seventhNumerator, seventhsFrame] <;>
        rw [abs_of_nonneg] <;> linarith

theorem sevenths_contourOK (a : Fin 6) : (seventhsFrameAt a).ContourOK := by
  refine ⟨?_, sevenths_contourGap a⟩
  fin_cases a <;> norm_num [seventhsFrameAt, seventhNumerator, seventhsFrame]

theorem sevenths_contour_floor (a : Fin 6) :
    ∀ i : Fin (seventhsFrameAt a).d,
      ((⌊(seventhsFrameAt a).xs - (seventhsFrameAt a).μ i⌋ : ℤ) : ℚ) +
        (seventhsFrameAt a).μ i ≤ (seventhsFrameAt a).n0off := by
  change ∀ i : Fin 2, _
  fin_cases a <;> decide

theorem sevenths_min_shift (a : Fin 6) :
    ∀ i : Fin (seventhsFrameAt a).d, (1 / 7 : ℝ) ≤ ((seventhsFrameAt a).μ i : ℝ) := by
  change ∀ i : Fin 2, (1 / 7 : ℝ) ≤ ((![(seventhNumerator a : ℚ) / 7, 1] i : ℚ) : ℝ)
  intro i
  fin_cases a <;> fin_cases i <;> norm_num [seventhNumerator]

#print axioms sevenths_contourGap
end CatalanCore.Uniform.Bank.Sevenths
