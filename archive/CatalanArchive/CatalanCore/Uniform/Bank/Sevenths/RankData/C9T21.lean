import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 03df5d19059cd32d5ebc3e81e2f35c0140c6532edf6c781d56c635728d56ce2a, root class 9. -/
def C9T21 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | 2 => (-39 / 44) | 3 => (-373 / 396) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | 2 => (-4293 / 1936) | 3 => (-354025 / 156816) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-6754637 / 7127109) | 3, 1 => (-2211076 / 7127109) | 3, 2 => (-4402 / 23997) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (6754637 / 7127109) | 3, 1 => (2211076 / 7127109) | 3, 2 => (4402 / 23997) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C9T21_ok : C9T21.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T21_den : ℕ := 7127109
theorem C9T21_den_ok :
    (∀ d ∈ C9T21.R, ∀ e ∈ C9T21.R, (C9T21.Lq d e).den ∣ C9T21_den ∧ (C9T21.Lq' d e).den ∣ C9T21_den) ∧
    (∀ d ∈ C9T21.C, ∀ e ∈ C9T21.C, (C9T21.Pq d e).den ∣ C9T21_den ∧ (C9T21.Pq' d e).den ∣ C9T21_den) := by
  constructor <;> decide +kernel
theorem C9T21_rload_3 : C9T21.rload 3 = ((-1048666 / 2375703), (-5194703 / 9502812)) := by decide +kernel
#print axioms C9T21_ok
#print axioms C9T21_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
