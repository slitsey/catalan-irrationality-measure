import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Fifths source type 70049b80bea2505d0dfbb195c0a12ae9403c3735994ca03a3d26c4663134a37a, prime class 9 mod 10. -/
def C9T12 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 4) | 2 => (-11 / 36) | 3 => (-83 / 252) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-9 / 16) | 2 => (-805 / 1296) | 3 => (-40489 / 63504) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-735163 / 880929) | 3, 1 => (-93868 / 293643) | 3, 2 => (-2734 / 13983) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (735163 / 880929) | 3, 1 => (93868 / 293643) | 3, 2 => (2734 / 13983) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C9T12_ok : C9T12.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T12_den : ℕ := 880929
theorem C9T12_den_ok :
    (∀ d ∈ C9T12.R, ∀ e ∈ C9T12.R, (C9T12.Lq d e).den ∣ C9T12_den ∧ (C9T12.Lq' d e).den ∣ C9T12_den) ∧
    (∀ d ∈ C9T12.C, ∀ e ∈ C9T12.C, (C9T12.Pq d e).den ∣ C9T12_den ∧ (C9T12.Pq' d e).den ∣ C9T12_den) := by
  constructor <;> decide +kernel
theorem C9T12_rload_3 : C9T12.rload 3 = ((-308080 / 880929), (-668467 / 3523716)) := by decide +kernel
#print axioms C9T12_ok
#print axioms C9T12_den_ok
end CatalanCore.Uniform.Bank.FifthsContent.RankData
