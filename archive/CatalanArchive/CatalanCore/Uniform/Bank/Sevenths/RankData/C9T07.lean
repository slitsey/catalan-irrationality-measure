import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 9b240adb5cb57f31d9dc2d1eb94eb53c9323689cd2f248ea236a32eac9e5a7d0, root class 9. -/
def C9T07 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | 2 => (-39 / 44) | 3 => (-373 / 396) | 4 => (-4811 / 4950) | 5 => (-78461 / 79200) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | 2 => (-4293 / 1936) | 3 => (-354025 / 156816) | 4 => (-13926499 / 6125625) | 5 => (-14309985001 / 6272640000) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T07_ok : C9T07.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T07_den : ℕ := 1
theorem C9T07_den_ok :
    (∀ d ∈ C9T07.R, ∀ e ∈ C9T07.R, (C9T07.Lq d e).den ∣ C9T07_den ∧ (C9T07.Lq' d e).den ∣ C9T07_den) ∧
    (∀ d ∈ C9T07.C, ∀ e ∈ C9T07.C, (C9T07.Pq d e).den ∣ C9T07_den ∧ (C9T07.Pq' d e).den ∣ C9T07_den) := by
  constructor <;> decide +kernel
#print axioms C9T07_ok
#print axioms C9T07_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
