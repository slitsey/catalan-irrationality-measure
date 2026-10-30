import CatalanCore.Uniform.Bank.Sevenths.Frame
import CatalanCore.Uniform.Bank.Sevenths.Final
import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.Member.FrameDigamma
import CatalanCore.Uniform.Content.BankShared.NormaliseFamily
set_option Elab.async false

namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.BankShared

/-- Norm-one frame for the actual q7 physical rank calculation. -/
def pipelineFrame (a : Fin 6) : Frame :=
  { seventhsFrameAt a with norm := 1, hnorm := by norm_num }

def u7 (a : Fin 6) : Fin 2 → ℕ := ![seventhNumerator a, 1]
def q7 : Fin 2 → ℕ := ![7, 1]

theorem hu7 (a : Fin 6) (i : Fin 2) :
    (pipelineFrame a).μ i = (u7 a i : ℚ) / q7 i := by
  fin_cases i <;> simp [pipelineFrame, seventhsFrameAt, seventhsFrame, u7, q7]

theorem hq7 (i : Fin 2) : 0 < q7 i := by
  fin_cases i <;> norm_num [q7]

theorem pipeline_digamma (a : Fin 6) :
    frameDigamma (pipelineFrame a) (u7 a) q7 = D7Frame (seventhNumerator a) := by
  unfold frameDigamma D7Frame
  congr 1
  funext i
  fin_cases i
  · change ((-1 : ℤ) : ℚ) / 1 = (-1 : ℚ)
    norm_num
  · change ((1 : ℤ) : ℚ) / 1 = (1 : ℚ)
    norm_num

theorem sevenths_Mn_normalise (a : Fin 6) (x y : ℕ) :
    (seventhsFrameAt a).Mn x y = (49 : ℚ)⁻¹ * (pipelineFrame a).Mn x y := by
  have hD : ∀ t, (seventhsFrameAt a).Delta t = (pipelineFrame a).Delta t := fun _ => rfl
  have hE : ∀ t, (seventhsFrameAt a).Dsq t = (pipelineFrame a).Dsq t := fun _ => rfl
  have hN : (seventhsFrameAt a).norm = 49 := rfl
  have hN0 : (pipelineFrame a).norm = 1 := rfl
  simp only [Frame.Mn, hD, hE, hN, hN0]
  split_ifs <;> norm_num <;> ring

theorem sevenths_const_normalise (a : Fin 6) :
    (seventhsFrameAt a).const = (((49 : ℚ)⁻¹ : ℚ) : ℝ) * (pipelineFrame a).const := by
  let t : ℝ := ∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℝ) *
    hurwitzTail2 (![(seventhNumerator a : ℚ) / 7, 1] i)
  change t / ((49 : ℚ) : ℝ) = (((49 : ℚ)⁻¹ : ℚ) : ℝ) * (t / ((1 : ℚ) : ℝ))
  push_cast
  ring

/-- Leading coefficient-content is preserved by the full polynomial normalization,
including every retained common subset. -/
theorem sevenths_content_normalise (a : Fin 6) (depth : ℕ)
    (H : HasScaledContent
      ((F7.family (pipelineFrame a) depth).restrictAdm (fun i => i.1 % 2 = 0))
      F7.scale Lam7) :
    HasScaledContent
      ((F7.family (seventhsFrameAt a) depth).restrictAdm (fun i => i.1 % 2 = 0))
      F7.scale Lam7 :=
  bank_content_normalise F7 (seventhsFrameAt a) (pipelineFrame a) depth
    (fun i => i.1 % 2 = 0) (N := 49) (by norm_num)
    (sevenths_Mn_normalise a) (sevenths_const_normalise a) H

#print axioms pipeline_digamma
#print axioms sevenths_Mn_normalise
#print axioms sevenths_content_normalise
end CatalanCore.Uniform.Bank.Sevenths
