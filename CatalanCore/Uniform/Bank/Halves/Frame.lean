import CatalanFrames.Thirds.Frame
import CatalanFrames.P6.Const
import Mathlib.NumberTheory.ZetaValues
import CatalanCore.Uniform.Content.BankShared.Inst.TwoTerm
set_option Elab.async false

namespace CatalanCore.Uniform.Bank.Halves
open CatalanCore
open CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.BankShared.Inst

/-- The half-shift frame, with norm four and the catalogue contour data. -/
def halves : Frame := CatalanFrames.Thirds.thirdsFrame (1 / 2) 4 (1 / 4) (1 / 4) 0
  (by norm_num) (by norm_num) (by norm_num)

theorem halves_w_ne (i : Fin halves.d) : halves.w i ≠ 0 := by
  fin_cases i <;> decide

theorem halves_const : halves.const = ((-1 / 12 : ℚ) : ℝ) * Real.pi ^ 2 := by
  have he : halves.const =
      (∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℝ) * hurwitzTail2 (![1 / 2, 1] i)) / ((4 : ℚ) : ℝ) := rfl
  rw [he, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [CatalanFrames.P6.hurwitz_one, CatalanFrames.P6.hurwitz_half, hasSum_zeta_two.tsum_eq]
  have hs := CatalanFrames.P6.split_two
  rw [hasSum_zeta_two.tsum_eq] at hs
  push_cast at hs ⊢
  nlinarith

theorem halves_twoTerm : TwoTermData halves 2 1 := by
  have he (t : ℕ) : (t : ℚ) - 1 + 1 / 2 = (2 * (t : ℚ) - 1) / 2 := by ring
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro t ht
    change (CatalanFrames.Thirds.thirdsFrame (1 / 2) 4 (1 / 4) (1 / 4) 0
      (by norm_num) (by norm_num) (by norm_num)).Delta t = _
    rw [CatalanFrames.Thirds.Delta_eq, he, one_div_div]
    norm_num
  · intro t ht
    change (CatalanFrames.Thirds.thirdsFrame (1 / 2) 4 (1 / 4) (1 / 4) 0
      (by norm_num) (by norm_num) (by norm_num)).Dsq t = _
    rw [CatalanFrames.Thirds.Dsq_eq, he, div_pow, one_div_div]
    norm_num

theorem halves_shift : CatalanFrames.Fifths.ShiftData halves 2 1 :=
  shift_ofTwoTerm (by norm_num) halves_twoTerm (by norm_num [halves, CatalanFrames.Thirds.thirdsFrame])

end CatalanCore.Uniform.Bank.Halves
