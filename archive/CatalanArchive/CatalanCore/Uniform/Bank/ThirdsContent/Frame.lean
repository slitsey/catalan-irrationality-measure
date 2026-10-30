import CatalanCore.Uniform.Bank.ThirdsContent.OfDebit
import CatalanCore.Uniform.Content.BankShared.NormaliseFamily
import CatalanFrames.Thirds.TargetConstants
set_option Elab.async false

/-! # Norm-one pipeline frames for the thirds bank (lane B, B4b)

The layer suppliers (M3D, LP, UF) are stated for norm-one two-term frames.  `pipeA`, `pipeB` have
the shifts and weights of `thirdsAc`, `thirdsBc` and norm `1`; the matrices differ by the factor
`1/9`, so content transports with the same constant (`thirds_content_from_pipe`). -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanFrames.Thirds
  CatalanCore.Uniform.Content.BankShared

/-- `ψ(z+1) - ψ(z+1/3)` with norm one. -/
def pipeA : Frame :=
  thirdsFrame (1 / 3) 1 (2 / 3) (1 / 3) 1 (by norm_num) (by norm_num) (by norm_num)

/-- `ψ(z+1) - ψ(z+2/3)` with norm one. -/
def pipeB : Frame :=
  thirdsFrame (2 / 3) 1 (1 / 3) (1 / 3) 0 (by norm_num) (by norm_num) (by norm_num)

theorem thirdsAc_Mn_pipe (a b : ℕ) : thirdsAc.Mn a b = (9 : ℚ)⁻¹ * pipeA.Mn a b := by
  have hD : ∀ k, thirdsAc.Dsq k = pipeA.Dsq k := fun k => rfl
  have hF : ∀ k, thirdsAc.Delta k = pipeA.Delta k := fun k => rfl
  simp only [Frame.Mn, hD, hF]
  have hn : thirdsAc.norm = 9 := rfl
  have hn' : pipeA.norm = 1 := rfl
  rw [hn, hn']
  split_ifs <;> ring

theorem thirdsBc_Mn_pipe (a b : ℕ) : thirdsBc.Mn a b = (9 : ℚ)⁻¹ * pipeB.Mn a b := by
  have hD : ∀ k, thirdsBc.Dsq k = pipeB.Dsq k := fun k => rfl
  have hF : ∀ k, thirdsBc.Delta k = pipeB.Delta k := fun k => rfl
  simp only [Frame.Mn, hD, hF]
  have hn : thirdsBc.norm = 9 := rfl
  have hn' : pipeB.norm = 1 := rfl
  rw [hn, hn']
  split_ifs <;> ring

theorem thirdsAc_const_pipe : thirdsAc.const = (((9 : ℚ)⁻¹ : ℚ) : ℝ) * pipeA.const := by
  have hS : (∑ i, (thirdsAc.w i : ℝ) * hurwitzTail2 (thirdsAc.μ i)) =
      ∑ i, (pipeA.w i : ℝ) * hurwitzTail2 (pipeA.μ i) := rfl
  have hn : thirdsAc.norm = 9 := rfl
  have hn' : pipeA.norm = 1 := rfl
  unfold Frame.const
  rw [hS, hn, hn']
  push_cast
  ring

theorem thirdsBc_const_pipe : thirdsBc.const = (((9 : ℚ)⁻¹ : ℚ) : ℝ) * pipeB.const := by
  have hS : (∑ i, (thirdsBc.w i : ℝ) * hurwitzTail2 (thirdsBc.μ i)) =
      ∑ i, (pipeB.w i : ℝ) * hurwitzTail2 (pipeB.μ i) := rfl
  have hn : thirdsBc.norm = 9 := rfl
  have hn' : pipeB.norm = 1 := rfl
  unfold Frame.const
  rw [hS, hn, hn']
  push_cast
  ring

/-- Content of the actual norm-9 frame from the norm-one pipeline frame (same `Λ`). -/
theorem thirds_content_from_pipeA (depth : ℕ) (Λ : ℝ)
    (h : HasScaledContent (FamE pipeA depth) G310.scale Λ) :
    HasScaledContent (FamE thirdsAc depth) G310.scale Λ :=
  bank_content_normalise G310 thirdsAc pipeA depth _ (by norm_num) thirdsAc_Mn_pipe
    thirdsAc_const_pipe h

theorem thirds_content_from_pipeB (depth : ℕ) (Λ : ℝ)
    (h : HasScaledContent (FamE pipeB depth) G310.scale Λ) :
    HasScaledContent (FamE thirdsBc depth) G310.scale Λ :=
  bank_content_normalise G310 thirdsBc pipeB depth _ (by norm_num) thirdsBc_Mn_pipe
    thirdsBc_const_pipe h


end CatalanCore.Uniform.Bank.ThirdsContent
