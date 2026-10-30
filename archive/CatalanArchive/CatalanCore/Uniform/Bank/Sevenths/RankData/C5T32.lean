import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 102b19d01f5da211ff02650b3cf2740d6d7e42a1a049cc895da6bc8cda21106a, root class 5. -/
def C5T32 : FibreCert where
  R := {0}
  C := {0}
  lf := fun d => match d with | 0 => (-7 / 3) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C5T32_ok : C5T32.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T32_den : ℕ := 1
theorem C5T32_den_ok :
    (∀ d ∈ C5T32.R, ∀ e ∈ C5T32.R, (C5T32.Lq d e).den ∣ C5T32_den ∧ (C5T32.Lq' d e).den ∣ C5T32_den) ∧
    (∀ d ∈ C5T32.C, ∀ e ∈ C5T32.C, (C5T32.Pq d e).den ∣ C5T32_den ∧ (C5T32.Pq' d e).den ∣ C5T32_den) := by
  constructor <;> decide +kernel
#print axioms C5T32_ok
#print axioms C5T32_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
