module

public import CatalanFrames.Lambda.Const
public import CatalanFrames.LambdaMirror.Const

@[expose] public section
set_option Elab.async false

namespace CatalanCore.Uniform.Bank.Fourths
open CatalanCore

/-- `true` is plus, `false` is minus. These are the original norm-16 frames. -/
def lambdaFrame (sgn : Bool) : Frame :=
  if sgn then CatalanFrames.LambdaMirror.mirFrame else CatalanFrames.Lambda.lamFrame

noncomputable def lambdaTarget (sgn : Bool) : ℝ :=
  (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) +
    (if sgn then 1 else -1) * (5 * Real.pi ^ 2 / 48)

theorem lambdaFrame_d (sgn : Bool) : (lambdaFrame sgn).d = 2 := by
  cases sgn <;> rfl

theorem lambdaFrame_w_ne (sgn : Bool) (i : Fin (lambdaFrame sgn).d) :
    (lambdaFrame sgn).w i ≠ 0 := by
  cases sgn
  · fin_cases i
    · change (-1 : ℤ) ≠ 0
      decide
    · change (1 : ℤ) ≠ 0
      decide
  · fin_cases i
    · change (1 : ℤ) ≠ 0
      decide
    · change (-1 : ℤ) ≠ 0
      decide

theorem lambdaFrame_const (sgn : Bool) :
    (lambdaFrame sgn).const = ((1 / 2 : ℚ) : ℝ) * lambdaTarget sgn := by
  cases sgn
  · change CatalanFrames.Lambda.lamFrame.const = _
    rw [CatalanFrames.Lambda.const_eq]
    simp only [lambdaTarget, Bool.false_eq_true, if_false]
    push_cast
    ring
  · change CatalanFrames.LambdaMirror.mirFrame.const = _
    rw [CatalanFrames.LambdaMirror.const_eq]
    simp only [lambdaTarget, if_true]
    push_cast
    ring

end CatalanCore.Uniform.Bank.Fourths
