import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 4d53ec778188866fe1f66592b5bcaa997e57ee393e446c2c0cada0d89089b372, prime class 3 mod 10. -/
def C3T13 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 2) | 2 => (-12 / 7) | 3 => (-151 / 84) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-21 / 4) | 2 => (-270 / 49) | 3 => (-4369 / 784) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T13_ok : C3T13.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T13_den : ℕ := 1
theorem C3T13_den_ok :
    (∀ d ∈ C3T13.R, ∀ e ∈ C3T13.R, (C3T13.Lq d e).den ∣ C3T13_den ∧ (C3T13.Lq' d e).den ∣ C3T13_den) ∧
    (∀ d ∈ C3T13.C, ∀ e ∈ C3T13.C, (C3T13.Pq d e).den ∣ C3T13_den ∧ (C3T13.Pq' d e).den ∣ C3T13_den) := by
  constructor <;> decide +kernel
#print axioms C3T13_ok
#print axioms C3T13_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
