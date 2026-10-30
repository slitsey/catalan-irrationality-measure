import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 15d8a947c768cd03e2fea561b80b02e570da7afa1d7d7ddc1167729fe7829600, prime class 7 mod 10. -/
def C7T27 : FibreCert where
  R := {0}
  C := ∅
  lf := fun d => match d with | 0 => (-5 / 3) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun _ _ => 0
  Pq' := fun _ _ => 0
  kr := {0}
  kc := ∅

theorem C7T27_ok : C7T27.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T27_den : ℕ := 1
theorem C7T27_den_ok :
    (∀ d ∈ C7T27.R, ∀ e ∈ C7T27.R, (C7T27.Lq d e).den ∣ C7T27_den ∧ (C7T27.Lq' d e).den ∣ C7T27_den) ∧
    (∀ d ∈ C7T27.C, ∀ e ∈ C7T27.C, (C7T27.Pq d e).den ∣ C7T27_den ∧ (C7T27.Pq' d e).den ∣ C7T27_den) := by
  constructor <;> decide +kernel
theorem C7T27_rload_0 : C7T27.rload 0 = (1, (-5 / 3)) := by decide +kernel
#print axioms C7T27_ok
#print axioms C7T27_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
