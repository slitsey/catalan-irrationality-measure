import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 803dc3f36711aff8d6eec3bc1e97fa1598f64b56d11f9c43b93fcdabc22446f4, root class 9. -/
def C9T20 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | 2 => (-39 / 44) | 3 => (-373 / 396) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | 2 => (-4293 / 1936) | 3 => (-354025 / 156816) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (-6754637 / 7127109) | 1, 1 => 1 | 1, 3 => (-2211076 / 7127109) | 2, 2 => 1 | 2, 3 => (-4402 / 23997) | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 3 => (6754637 / 7127109) | 1, 1 => 1 | 1, 3 => (2211076 / 7127109) | 2, 2 => 1 | 2, 3 => (4402 / 23997) | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := {3}

theorem C9T20_ok : C9T20.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T20_den : ℕ := 7127109
theorem C9T20_den_ok :
    (∀ d ∈ C9T20.R, ∀ e ∈ C9T20.R, (C9T20.Lq d e).den ∣ C9T20_den ∧ (C9T20.Lq' d e).den ∣ C9T20_den) ∧
    (∀ d ∈ C9T20.C, ∀ e ∈ C9T20.C, (C9T20.Pq d e).den ∣ C9T20_den ∧ (C9T20.Pq' d e).den ∣ C9T20_den) := by
  constructor <;> decide +kernel
theorem C9T20_cload_3 : C9T20.cload 3 = ((-1048666 / 2375703), (-5194703 / 9502812)) := by decide +kernel
#print axioms C9T20_ok
#print axioms C9T20_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
