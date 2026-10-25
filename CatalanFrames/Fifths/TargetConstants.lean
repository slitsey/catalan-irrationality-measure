module
public import CatalanFrames.Fifths.ContourInstances
public import CatalanFrames.P6.Const
public import CatalanCore.Decay.Atoms
public import Mathlib.NumberTheory.ZetaValues
@[expose] public section
open CatalanCore
namespace CatalanFrames.Fifths
/-- The requested target, defined directly by its convergent real series. -/
noncomputable def fifthsTarget (a : ℕ) : ℝ :=
  (∑' n : ℕ, 1/((n : ℝ)+(((a : ℚ)/5 : ℚ) : ℝ))^2)-Real.pi^2/6
theorem fifthsTarget_summable (a : ℕ) (ha : 0 < a) :
    Summable (fun n : ℕ => 1/((n : ℝ)+(((a : ℚ)/5 : ℚ) : ℝ))^2) := by
  apply Frame.summable_inv_sq_add'
  positivity
/-- No special Hurwitz-at-fifths value or conductor-five L-value identity is required. -/
theorem shiftFrame_const (s xs δ0 : ℚ) (n0 : ℕ) (hs0 : 0 < s) (hs1 : s < 1) :
    (Thirds.thirdsFrame s 25 xs δ0 n0 hs0 hs1 (by norm_num)).const =
      ((-1/25 : ℚ) : ℝ)*(hurwitzTail2 s-Real.pi^2/6) := by
  have he : (Thirds.thirdsFrame s 25 xs δ0 n0 hs0 hs1 (by norm_num)).const =
      (∑ i : Fin 2, ((![-1,1] i : ℤ) : ℝ)*hurwitzTail2 (![s,1] i))/((25 : ℚ) : ℝ) := rfl
  rw [he,Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
  rw [CatalanFrames.P6.hurwitz_one,hasSum_zeta_two.tsum_eq]
  push_cast
  ring
theorem fifths1_const : fifths1.const = ((-1/25 : ℚ) : ℝ)*fifthsTarget 1 := by
  simpa [fifths1,fifthsTarget,hurwitzTail2] using
    shiftFrame_const (1/5) (3/5) (1/4) 1 (by norm_num) (by norm_num)
theorem fifths2_const : fifths2.const = ((-1/25 : ℚ) : ℝ)*fifthsTarget 2 := by
  simpa [fifths2,fifthsTarget,hurwitzTail2] using
    shiftFrame_const (2/5) (7/10) (1/4) 1 (by norm_num) (by norm_num)
theorem fifths3_const : fifths3.const = ((-1/25 : ℚ) : ℝ)*fifthsTarget 3 := by
  simpa [fifths3,fifthsTarget,hurwitzTail2] using
    shiftFrame_const (3/5) (3/10) (1/4) 0 (by norm_num) (by norm_num)
theorem fifths4_const : fifths4.const = ((-1/25 : ℚ) : ℝ)*fifthsTarget 4 := by
  simpa [fifths4,fifthsTarget,hurwitzTail2] using
    shiftFrame_const (4/5) (2/5) (1/4) 0 (by norm_num) (by norm_num)
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.fifths1_const
#print axioms CatalanFrames.Fifths.fifths2_const
#print axioms CatalanFrames.Fifths.fifths3_const
#print axioms CatalanFrames.Fifths.fifths4_const
