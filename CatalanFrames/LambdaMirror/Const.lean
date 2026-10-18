module

public import CatalanFrames.LambdaMirror.Frame
public import CatalanLambda.Mirror.LambdaCatalan

/-!
# `mirFrame.const = λ' = G/2 + 5π²/96`
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.LambdaMirror

theorem const_eq_lamB : mirFrame.const = CatalanLambda.Mirror.lamB := by
  have hA := CatalanLambda.Decay.summable_inv_sq_add (1 / 4) (by norm_num)
  have hB := CatalanLambda.Decay.summable_inv_sq_add 1 (by norm_num)
  have e : mirFrame.const = (hurwitzTail2 (1 / 4) - hurwitzTail2 1) / 16 := by
    have : ∑ i : Fin 2, ((![1, -1] i : ℤ) : ℝ) * hurwitzTail2 (![1 / 4, 1] i)
        = hurwitzTail2 (1 / 4) - hurwitzTail2 1 := by
      rw [Fin.sum_univ_two]; simp; ring
    exact congrArg (· / (16 : ℝ)) this
  rw [e]
  unfold hurwitzTail2 CatalanLambda.Mirror.lamB
  push_cast
  have hk : ∀ k : ℕ, (1 / (4 * (k : ℝ) + 1) ^ 2 - 1 / (16 * ((k : ℝ) + 1) ^ 2))
      = (1 / 16) * (1 / ((k : ℝ) + 1 / 4) ^ 2) - (1 / 16) * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((k : ℝ) + 1 / 4) ≠ 0 := by positivity
    have h3 : (4 * (k : ℝ) + 1) = 4 * ((k : ℝ) + 1 / 4) := by ring
    rw [h3]
    field_simp
    ring
  rw [tsum_congr hk, Summable.tsum_sub (hA.mul_left _) (hB.mul_left _), tsum_mul_left,
    tsum_mul_left]
  ring

theorem const_eq : mirFrame.const = (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
    + 5 * Real.pi ^ 2 / 96 := by
  rw [const_eq_lamB]; exact CatalanLambda.Mirror.lamB_eq

end CatalanFrames.LambdaMirror
