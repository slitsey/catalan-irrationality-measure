import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 5d12fbe38c9e6846cfd27f2aea5caa8e7c43b849b0ba6639d9358b8931251a74, prime class 9 mod 10. -/
def C9T23 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 4) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-9 / 16) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C9T23_ok : C9T23.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T23_den : ℕ := 1
theorem C9T23_den_ok :
    (∀ d ∈ C9T23.R, ∀ e ∈ C9T23.R, (C9T23.Lq d e).den ∣ C9T23_den ∧ (C9T23.Lq' d e).den ∣ C9T23_den) ∧
    (∀ d ∈ C9T23.C, ∀ e ∈ C9T23.C, (C9T23.Pq d e).den ∣ C9T23_den ∧ (C9T23.Pq' d e).den ∣ C9T23_den) := by
  constructor <;> decide +kernel
theorem C9T23_cload_1 : C9T23.cload 1 = (1, 0) := by decide +kernel
#print axioms C9T23_ok
#print axioms C9T23_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
