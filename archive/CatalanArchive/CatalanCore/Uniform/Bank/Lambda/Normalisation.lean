import CatalanCore.Uniform.Bank.Lambda.Frame
import CatalanCore.Uniform.Bank.Lambda.Pipeline
import CatalanCore.Uniform.Bank.Lambda.Geom
import CatalanCore.Uniform.Content.BankShared.NormaliseFamily
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Uniform
  CatalanCore.Uniform.Content.BankShared

def pipelineNum (sgn : Bool) : ℕ := if sgn then 1 else 3

theorem pipelineNum_valid (sgn : Bool) : pipelineNum sgn = 1 ∨ pipelineNum sgn = 3 := by
  cases sgn <;> decide

def pipeline (sgn : Bool) : Frame := pipelineFrame (pipelineNum sgn) (pipelineNum_valid sgn)
def lambdaScale (sgn : Bool) : ℚ := if sgn then -16 else 16

theorem lambdaScale_ne_zero (sgn : Bool) : lambdaScale sgn ≠ 0 := by
  cases sgn <;> norm_num [lambdaScale]

theorem lambda_Mn_pipeline (sgn : Bool) (a b : ℕ) :
    (lambdaFrame sgn).Mn a b = (lambdaScale sgn)⁻¹ * (pipeline sgn).Mn a b := by
  cases sgn
  · have hD : ∀ k, (lambdaFrame false).Dsq k = (pipeline false).Dsq k := by
      intro k
      rfl
    have hF : ∀ k, (lambdaFrame false).Delta k = (pipeline false).Delta k := by
      intro k
      rfl
    simp only [Frame.Mn, hD, hF]
    norm_num [lambdaFrame, pipeline, pipelineNum, pipelineFrame, lambdaScale,
      CatalanFrames.Lambda.lamFrame]
    all_goals split_ifs <;> ring
  · have hD : ∀ k, (lambdaFrame true).Dsq k = -(pipeline true).Dsq k := by
      intro k
      change (∑ i : Fin 2, ((![1, -1] i : ℤ) : ℚ) /
        ((k : ℚ) - 1 + ![(1 / 4 : ℚ), 1] i) ^ 2) =
        -(∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℚ) /
          ((k : ℚ) - 1 + ![(1 / 4 : ℚ), 1] i) ^ 2)
      rw [Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Int.cast_one, Int.cast_neg]
      ring
    have hF : ∀ k, (lambdaFrame true).Delta k = -(pipeline true).Delta k := by
      intro k
      change (∑ i : Fin 2, ((![1, -1] i : ℤ) : ℚ) /
        ((k : ℚ) - 1 + ![(1 / 4 : ℚ), 1] i)) =
        -(∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℚ) /
          ((k : ℚ) - 1 + ![(1 / 4 : ℚ), 1] i))
      rw [Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Int.cast_one, Int.cast_neg]
      ring
    simp only [Frame.Mn, hD, hF, Finset.sum_neg_distrib]
    norm_num [lambdaFrame, pipeline, pipelineNum, pipelineFrame, lambdaScale,
      CatalanFrames.LambdaMirror.mirFrame]
    all_goals split_ifs <;> ring

theorem lambda_const_pipeline (sgn : Bool) :
    (lambdaFrame sgn).const = (((lambdaScale sgn)⁻¹ : ℚ) : ℝ) * (pipeline sgn).const := by
  cases sgn
  · change (∑ i : Fin 2, ((lambdaFrame false).w i : ℝ) *
        hurwitzTail2 ((lambdaFrame false).μ i)) / ((lambdaFrame false).norm : ℝ) =
      (((lambdaScale false)⁻¹ : ℚ) : ℝ) *
        ((∑ i : Fin 2, ((pipeline false).w i : ℝ) * hurwitzTail2 ((pipeline false).μ i)) /
          ((pipeline false).norm : ℝ))
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    have hw0 : (pipeline false).w (0 : Fin 2) = (lambdaFrame false).w (0 : Fin 2) := rfl
    have hw1 : (pipeline false).w (1 : Fin 2) = (lambdaFrame false).w (1 : Fin 2) := rfl
    have hm0 : (pipeline false).μ (0 : Fin 2) = (lambdaFrame false).μ (0 : Fin 2) := by
      change ((3 : ℕ) : ℚ) / 4 = (3 / 4 : ℚ)
      norm_num
    have hm1 : (pipeline false).μ (1 : Fin 2) = (lambdaFrame false).μ (1 : Fin 2) := rfl
    rw [hw0, hw1, hm0, hm1]
    norm_num [lambdaFrame, pipeline, pipelineNum, pipelineFrame, lambdaScale,
      CatalanFrames.Lambda.lamFrame, CatalanFrames.LambdaMirror.mirFrame]
    <;> ring
  · change (∑ i : Fin 2, ((lambdaFrame true).w i : ℝ) *
        hurwitzTail2 ((lambdaFrame true).μ i)) / ((lambdaFrame true).norm : ℝ) =
      (((lambdaScale true)⁻¹ : ℚ) : ℝ) *
        ((∑ i : Fin 2, ((pipeline true).w i : ℝ) * hurwitzTail2 ((pipeline true).μ i)) /
          ((pipeline true).norm : ℝ))
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    have hw0 : (lambdaFrame true).w (0 : Fin 2) = -(pipeline true).w (0 : Fin 2) := rfl
    have hw1 : (lambdaFrame true).w (1 : Fin 2) = -(pipeline true).w (1 : Fin 2) := rfl
    have hm0 : (lambdaFrame true).μ (0 : Fin 2) = (pipeline true).μ (0 : Fin 2) := by
      change (1 / 4 : ℚ) = ((1 : ℕ) : ℚ) / 4
      norm_num
    have hm1 : (lambdaFrame true).μ (1 : Fin 2) = (pipeline true).μ (1 : Fin 2) := rfl
    rw [hw0, hw1, hm0, hm1]
    norm_num [lambdaFrame, pipeline, pipelineNum, pipelineFrame, lambdaScale,
      CatalanFrames.Lambda.lamFrame, CatalanFrames.LambdaMirror.mirFrame]
    <;> ring

/-- Concrete norm/sign transport on the same retained-set family and the same scale. -/
theorem lambda_content_from_pipeline (sgn : Bool) (depth : ℕ) (Λ : ℝ)
    (h : HasScaledContent ((FL.family (pipeline sgn) depth).restrictAdm
      (fun i => i.1 % 2 = 0)) FL.scale Λ) :
    HasScaledContent ((FL.family (lambdaFrame sgn) depth).restrictAdm
      (fun i => i.1 % 2 = 0)) FL.scale Λ :=
  bank_content_normalise FL (lambdaFrame sgn) (pipeline sgn) depth _
    (lambdaScale_ne_zero sgn) (lambda_Mn_pipeline sgn) (lambda_const_pipeline sgn) h

#print axioms lambda_Mn_pipeline
#print axioms lambda_content_from_pipeline
end CatalanCore.Uniform.Bank.Lambda

