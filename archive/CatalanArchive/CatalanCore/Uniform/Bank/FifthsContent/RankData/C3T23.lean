import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type ed8aaed03d78ea773415062452380b4bab160ca25a1eeee29bb5d382d5b0ef8a, prime class 3 mod 10. -/
def C3T23 : FibreCert where
  R := {0}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-5 / 2) | 1 => (-31 / 14) | _ => 0
  ee := fun d => match d with | 0 => (-25 / 4) | 1 => (-1129 / 196) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (-8 / 175) | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 0, 1 => (8 / 175) | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := {1}

theorem C3T23_ok : C3T23.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T23_den : ℕ := 175
theorem C3T23_den_ok :
    (∀ d ∈ C3T23.R, ∀ e ∈ C3T23.R, (C3T23.Lq d e).den ∣ C3T23_den ∧ (C3T23.Lq' d e).den ∣ C3T23_den) ∧
    (∀ d ∈ C3T23.C, ∀ e ∈ C3T23.C, (C3T23.Pq d e).den ∣ C3T23_den ∧ (C3T23.Pq' d e).den ∣ C3T23_den) := by
  constructor <;> decide +kernel
theorem C3T23_cload_1 : C3T23.cload 1 = ((167 / 175), (-21 / 10)) := by decide +kernel
#print axioms C3T23_ok
#print axioms C3T23_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
