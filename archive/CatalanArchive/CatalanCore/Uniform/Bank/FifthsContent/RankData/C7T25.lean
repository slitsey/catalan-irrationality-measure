import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type dba30fc6ef86c09b7753fd8fe70d21910702591e647104cc7106a1b920d9c822, prime class 7 mod 10. -/
def C7T25 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 3) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-16 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C7T25_ok : C7T25.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C7T25_den : ℕ := 1
theorem C7T25_den_ok :
    (∀ d ∈ C7T25.R, ∀ e ∈ C7T25.R, (C7T25.Lq d e).den ∣ C7T25_den ∧ (C7T25.Lq' d e).den ∣ C7T25_den) ∧
    (∀ d ∈ C7T25.C, ∀ e ∈ C7T25.C, (C7T25.Pq d e).den ∣ C7T25_den ∧ (C7T25.Pq' d e).den ∣ C7T25_den) := by
  constructor <;> decide +kernel
theorem C7T25_rload_1 : C7T25.rload 1 = (1, 0) := by decide +kernel
#print axioms C7T25_ok
#print axioms C7T25_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
