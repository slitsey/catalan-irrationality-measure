import CatalanCore.Uniform.Bank.Fourths.PolePalette
import CatalanCore.Uniform.Content.Member.FrameDigamma
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Fourths
open CatalanCore CatalanCore.Uniform.Content.Member

/-- Norm-one positive pipeline frame, with the matching physical contour data. -/
def pipelineFrame (a : ℕ) (ha : a = 1 ∨ a = 3) : Frame where
  d := 2
  μ := ![(a : ℚ) / 4, 1]
  w := ![-1, 1]
  norm := 1
  xs := if a = 1 then 5 / 8 else 3 / 8
  δ0 := 3 / 8
  n0off := if a = 1 then 1 else 0
  hμ := by
    intro i
    rcases ha with rfl | rfl <;> fin_cases i <;> norm_num
  hμinj := by
    intro i j h
    rcases ha with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp_all <;> norm_num
  hw := by simp [Fin.sum_univ_two]
  hnorm := by norm_num

def u4 (a : ℕ) : Fin 2 → ℕ := ![a, 1]
def q4 : Fin 2 → ℕ := ![4, 1]

theorem hu4 (a : ℕ) (ha : a = 1 ∨ a = 3) (i : Fin 2) :
    (pipelineFrame a ha).μ i = (u4 a i : ℚ) / q4 i := by
  fin_cases i <;> simp [pipelineFrame, u4, q4]

theorem hq4 (i : Fin 2) : 0 < q4 i := by
  fin_cases i <;> norm_num [q4]

theorem pipeline_digamma (a : ℕ) (ha : a = 1 ∨ a = 3) :
    frameDigamma (pipelineFrame a ha) (u4 a) q4 = D4 a := by
  unfold frameDigamma D4
  congr 1
  funext i
  fin_cases i
  · change ((-1 : ℤ) : ℚ) / 1 = (-1 : ℚ)
    norm_num
  · change ((1 : ℤ) : ℚ) / 1 = (1 : ℚ)
    norm_num

#print axioms pipeline_digamma
end CatalanCore.Uniform.Bank.Fourths
