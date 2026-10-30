import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type da000df77461c2f6ca8db50447d0f630942520c7208ec9ad73582e9c96900e0f, prime class 7 mod 10. -/
def C7T18 : FibreCert where
  R := {0, 1}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 3) | 2 => (-19 / 24) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-16 / 9) | 2 => (-1105 / 576) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (-85 / 48) | 1, 1 => 1 | 1, 2 => (-19 / 32) | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 2 => (85 / 48) | 1, 1 => 1 | 1, 2 => (19 / 32) | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := {2}

theorem C7T18_ok : C7T18.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T18_den : ℕ := 96
theorem C7T18_den_ok :
    (∀ d ∈ C7T18.R, ∀ e ∈ C7T18.R, (C7T18.Lq d e).den ∣ C7T18_den ∧ (C7T18.Lq' d e).den ∣ C7T18_den) ∧
    (∀ d ∈ C7T18.C, ∀ e ∈ C7T18.C, (C7T18.Pq d e).den ∣ C7T18_den ∧ (C7T18.Pq' d e).den ∣ C7T18_den) := by
  constructor <;> decide +kernel
theorem C7T18_cload_2 : C7T18.cload 2 = ((-131 / 96), (-19 / 48)) := by decide +kernel
#print axioms C7T18_ok
#print axioms C7T18_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
